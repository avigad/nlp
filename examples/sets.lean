import data.set
open set classical

variable {X : Type}
variables A B C D : set X

-- Here is a short, though laconic, Lean proof of Proposition 0.1.

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
eq_of_subset_of_subset
  (take x,
    suppose x ∈ A ∪ (B ∩ C),
    or.elim this
      (suppose x ∈ A, and.intro (or.inl this) (or.inl this))
      (suppose x ∈ B ∩ C, and.intro (or.inr (and.left this)) (or.inr (and.right this))))
  (take x,
    assume H : x ∈ (A ∪ B) ∩ (A ∪ C),
    by_cases
      (suppose x ∈ A, or.inl this)
      (suppose x ∉ A,
        or.inr (and.intro
          (or_resolve_right (and.left H) this)
          (or_resolve_right (and.right H) this))))

-- Here is what could hopefully be inferred from the text.
-- Notice that the text proof does not say what is proved in "case1" and "case2",
--   it just does it.
-- From the structure of the proof, Lean can infer the placeholders, that is,
--   the values that should be assigned to the underscores.

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
have H1 : _, from
  take x,    -- not explicitly introduced in the text
  suppose x ∈ A ∪ (B ∩ C),
  have x ∈ A ∨ x ∈ B ∩ C, from sorry,
  have case1 : _, from
    suppose x ∈ A,    -- here we have to guess that we are splitting the "or"
    have x ∈ A ∪ B, from sorry,
    have x ∈ A ∪ C, from sorry,
    show x ∈ (A ∪ B) ∩ (A ∪ C), from sorry,
  have case2 : _, from
    suppose x ∈ B ∩ C,    -- the second component of the "or"
    have x ∈ B, from sorry,
    have x ∈ C, from sorry,
    have x ∈ A ∪ B, from sorry,
    have x ∈ A ∪ C, from sorry,
    show x ∈ (A ∪ B) ∩ (A ∪ C), from sorry,
  show x ∈ (A ∪ B) ∩ (A ∪ C), from sorry,   -- this is hard. because this is the
                                            -- conclusion of each case, it must be the
                                            -- conclusion of the first paragraph
have H2 : _, from
  take x,    -- again, not explicitly introduced in the text
  suppose x ∈ (A ∪ B) ∩ (A ∪ C),
  have x ∈ A ∪ B, from sorry,
  have x ∈ A ∪ C, from sorry,
  have case1 : _, from     -- the "If x is in A" suggests a case split
    suppose x ∈ A,
    show x ∈ A ∪ (B ∩ C), from sorry,
  have case2 : _, from     -- the "If x is not in A" case
    suppose x ∉ A,
    have x ∈ B, using `x ∈ A ∪ B`, from sorry,
    have x ∈ C, using `x ∈ A ∪ C`, from sorry,
    have x ∈ B ∩ C, from sorry,
    show x ∈ A ∪ (B ∩ C), from sorry,
  show x ∈ A ∩ (B ∪ C), from sorry,
show A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C), from sorry

-- The details can be filled in, as follows.

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
have H1 : _, from
  take x,
  suppose x ∈ A ∪ (B ∩ C),
  have H1e : x ∈ A ∨ x ∈ B ∩ C, from this,
  have case1 : _, from
    suppose x ∈ A,    -- here we have to guess that we are splitting the "or"
    have H1a : x ∈ A ∪ B, from or.inl `x ∈ A`,
    have H1b : x ∈ A ∪ C, from or.inl `x ∈ A`,
    show x ∈ (A ∪ B) ∩ (A ∪ C), from and.intro H1a H1b,
  have case2 : _, from
    suppose x ∈ B ∩ C,    -- the second component of the "or"
    have x ∈ B, from and.left `x ∈ B ∩ C`,
    have x ∈ C, from and.right `x ∈ B ∩ C`,
    have H1c : x ∈ A ∪ B, from or.inr `x ∈ B`,
    have H1d : x ∈ A ∪ C, from or.inr `x ∈ C`,
    show x ∈ (A ∪ B) ∩ (A ∪ C), from and.intro H1c H1d,
  show x ∈ (A ∪ B) ∩ (A ∪ C), from or.elim H1e case1 case2,
have H2 : _, from
  take x,    -- again, not explicitly introduced in the text
  assume H2a : x ∈ (A ∪ B) ∩ (A ∪ C),
  have x ∈ A ∪ B, from and.left H2a,
  have x ∈ A ∪ C, from and.right H2a,
  have case1 : _, from     -- the "If x is in A" suggests a case split
    suppose x ∈ A,
    show x ∈ A ∪ (B ∩ C), from or.inl this,
  have case2 : _, from     -- the "If x is not in A" case
    suppose x ∉ A,
    have x ∈ B, from or_resolve_right `x ∈ A ∪ B` `x ∉ A`,
    have x ∈ C, from or_resolve_right `x ∈ A ∪ C` `x ∉ A`,
    have x ∈ B ∩ C, from and.intro `x ∈ B` `x ∈ C`,
    show x ∈ A ∪ (B ∩ C), from or.inr this,
  show x ∈ A ∪ (B ∩ C), from by_cases case1 case2,
show A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C), from eq_of_subset_of_subset H1 H2

-- Here is a complete Lean proof of Proposition 0.2.

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
eq_of_subset_of_subset
  (take x,
    assume H : x ∈ A ∩ (B ∪ C),
    have x ∈ A, from and.left H,
    have x ∈ B ∪ C, from and.right H,
    or.elim (`x ∈ B ∪ C`)
      (suppose x ∈ B,
        have x ∈ A ∩ B, from and.intro `x ∈ A` `x ∈ B`,
        show x ∈ (A ∩ B) ∪ (A ∩ C), from or.inl this)
      (suppose x ∈ C,
        have x ∈ A ∩ C, from and.intro `x ∈ A` `x ∈ C`,
        show x ∈ (A ∩ B) ∪ (A ∩ C), from or.inr this))
  (take x,
    suppose x ∈ (A ∩ B) ∪ (A ∩ C),
    or.elim this
      (assume H : x ∈ A ∩ B,
        have x ∈ A, from and.left H,
        have x ∈ B, from and.right H,
        have x ∈ B ∪ C, from or.inl this,
        show x ∈ A ∩ (B ∪ C), from and.intro `x ∈ A` this)
      (assume H : x ∈ A ∩ C,
        have x ∈ A, from and.left H,
        have x ∈ C, from and.right H,
        have x ∈ B ∪ C, from or.inr this,
        show x ∈ A ∩ (B ∪ C), from and.intro `x ∈ A` this))

-- Here is a complete Lean proof of Proposition 0.3

example : -(A \ B) = -A ∪ B :=
eq_of_subset_of_subset
  (take x,
    assume H : x ∉ A \ B,
    by_cases
      (suppose x ∈ A,
        have x ∈ B, from by_contradiction
         (suppose x ∉ B,
           have x ∈ A \ B, from and.intro `x ∈ A` this,
           show false, from H this),
        show x ∈ -A ∪ B, from or.inr this)
      (suppose x ∉ A, or.inl this))
  (take x,
    suppose x ∈ -A ∪ B,
        or.elim this
      (suppose x ∉ A,
        show x ∉ A \ B, from assume H, this (and.left H))
      (suppose x ∈ B,
        show x ∉ A \ B, from assume H, and.right H this))

-- IOU proposition 0.4

-- Here is a proof of Proposition 0.5

definition disjoint (A B : set X) : Prop := A ∩ B = ∅

example (H : disjoint A B) (H1 : C ⊆ A) (H2 : D ⊆ B) : disjoint C D :=
eq_empty_of_forall_not_mem
  (take x,
    suppose x ∈ C ∩ D,
    obtain (H3 : x ∈ C) (H4 : x ∈ D), from this,
    have x ∈ A ∩ B, from and.intro (H1 H3) (H2 H4),
    have x ∈ ∅, from eq.subst H this,
    show false, from this)
