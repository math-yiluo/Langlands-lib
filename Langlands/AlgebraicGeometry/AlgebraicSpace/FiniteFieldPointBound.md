# A bound on field-valued points of a finite morphism over a point

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteFieldPointBound`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace`.

- `exists_card_le_of_isFinite p η`. Let `p : R ⟶ U` be a finite morphism of schemes and `η` a
  point of `U`. Then there is `N` with the following property. For every field `K`, every
  `α : κ(η) ⟶ K` and every injective family `r : Fin m → (Spec K ⟶ R)` with
  `r j ≫ p = Spec α ≫ (Spec κ(η) ⟶ U)` for all `j`, we have `m ≤ N`.

Proof.

1. Let `F` be the scheme-theoretic fibre `p.fiber η`. Its map to `Spec κ(η)` is a base change
   of `p` (`MorphismProperty.of_isPullback`), so it is finite and `F` is affine.
2. Each `r j` lifts uniquely to `s j : Spec K ⟶ F` over `Spec α`.
3. The ring maps `Γ(F) ⟶ K` induced by `s j` are `κ(η)`-algebra maps, by
   `Scheme.ΓSpecIso_naturality`. They are pairwise distinct by `ext_of_isAffine`.
4. Their number is at most `finrank κ(η) Γ(F)`, by Mathlib's `card_algHom_le_finrank`
   (Dedekind independence). This bound depends only on `p` and `η`.

Provenance: internal helper for bounding the length of tuples of pairwise distinct
field-valued points with a common image. The argument is the standard Dedekind-independence
bound; no source proof is transcribed.
