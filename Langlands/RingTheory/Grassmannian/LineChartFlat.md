# Flatness of the Grassmannian of rank-one quotients of a finite projective module

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.RingTheory.Grassmannian.LineChartFlat`, and
`Module.Grassmannian.ProjectiveEmbedding.Rep.flat_p`.

- `exists_retract`, `flat_symmetricAlgebra`: for a finite projective `R`-module `M`, Mathlib's
  `SymmetricAlgebra R M` is an algebra retract of the symmetric algebra of a free module of finite
  rank (a polynomial ring, `SymmetricAlgebra.equivMvPolynomial`), hence flat.
- `isDomain_tensor`: for every field `K` over `R`, `K ⊗ Sym M` embeds into the polynomial ring
  `K[x₁, …, xₙ]` (Mathlib's `MvPolynomial.algebraTensorAlgEquiv`), so it is a domain.
- `one_tmul_ne_zero`: `1 ⊗ (ι v - 1) ≠ 0` in `K ⊗ Sym M` (the augmentation `ι v ↦ 0` sends it to
  `-1`).
- `flat_chartAlgebra`: for `R` noetherian, the Library's chart algebra
  `Module.Grassmannian.ChartAlgebra.S R x` of rank one, which is `Sym(Fin 1 → M) ⧸ (ι x - 1)`, is
  flat over `R`. This is `FibrewiseRegular.regular_and_flat_quotient`, whose fibre hypothesis
  comes from `isDomain_tensor`, `one_tmul_ne_zero` and
  `FibreLocalDomain.isSMulRegular_of_isDomain_fiber`.
- `Rep.flat_p`: a representing scheme `D.Gr` of the Grassmannian of rank-one quotients of a finite
  projective module over a noetherian ring is flat over `Spec R`. Flatness is local on the source;
  on the affine charts `D.V x` the coordinate ring is the chart algebra (Library
  `chartAlgEquiv`), as in the Library's proof of `Rep.locallyOfFinitePresentation_p`.

## Source

When `Q` is locally free, `P(Q)` is locally a projective space over the base, hence flat
(Kleiman, *The Picard scheme*, p.30, proof of Theorem 4.8). This file proves flatness of the
representing scheme for finite projective `Q` directly through its charts.
