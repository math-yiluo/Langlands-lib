# Galois theory of restriction along closure embeddings

This module proves elementary Galois-theoretic facts about
`restrictionAlongClosure` from `Langlands.Galois.ClosureRestriction`. For a
field extension `E/K` and a `K`-algebra embedding `ι : K̄ → Ē` of algebraic
closures, `restrictionAlongClosure ι g` is the automorphism `h` of `K̄` with
`ι ∘ h = g ∘ ι`.

## Contents

- `eq_restrictionAlongClosure`: an automorphism `h` of `K̄` with
  `ι (h x) = g (ι x)` for all `x` is `restrictionAlongClosure ι g`. The proof
  uses injectivity of `ι` and `restrictionAlongClosure_commutes`.
- `restrictionAlongClosure_comp_aut`: restriction along `ι ∘ c`, for
  `c ∈ Gal(K̄/K)`, is `c⁻¹ · r_ι(g) · c`.
- `restrictionAlongClosure_congr`: pointwise equal embeddings give equal
  restrictions.
- `closureEmbedding_bijective` and `closureEmbeddingRingEquiv`: for an algebraic
  extension `E/K` every closure embedding is bijective. `Ē` is algebraic over
  `K` by transitivity, and Mathlib's `Algebra.IsAlgebraic.algHom_bijective₂`
  applies to a pair of `K`-embeddings in opposite directions.
- `mem_range_restrictionAlongClosure_iff_fixes_preimages`: for algebraic `E/K`, an element `g`
  of `Gal(K̄/K)` lies in the image of the restriction exactly when it fixes
  every `y ∈ K̄` that `ι` sends into `E`. In the converse direction, the
  conjugate `ι ∘ g ∘ ι⁻¹` fixes `E` and is an element of `Gal(Ē/E)`, and its
  restriction is `g` by `eq_restrictionAlongClosure`.
- `restrictionAlongClosure_comp`: for a tower `K ⊆ E ⊆ F` and embeddings
  `ι₁ : K̄ → Ē`, `ι₂ : Ē → F̄` and `ι = ι₂ ∘ ι₁`, restriction along `ι` is the
  composite of the two restrictions.
- `restrictionAlongClosureHom`, `eq_restrictionAlongClosureHom`,
  `closureEmbeddingOfRingHom` and `eq_restrictionAlongClosureHom_ofRingHom`:
  the same restriction for a field homomorphism `f : K → E` with the algebra
  structure induced by `f`. A ring homomorphism `φ : K̄ → Ē` that extends `f`
  is a closure embedding compatible with `f`. These forms are used when `E` is
  regarded as a `K`-algebra through a twisted embedding, which differs from
  any algebra instance already present.

All statements are standard Galois theory of algebraic closures, and no
hypothesis beyond the displayed algebraicity is needed.
