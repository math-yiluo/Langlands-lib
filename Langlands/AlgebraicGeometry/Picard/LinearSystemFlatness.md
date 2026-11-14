# Flatness of the linear system when the fibres have no `H¹`

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule`.

- `resAlg p`, `specMap_resAlg`, `ker_resAlg`: the residue field at a point `p` of `Spec R` as an
  `R`-algebra, with `specMap = fromSpecResidueField p` and kernel `p`.
- `isPullback_of_eq`, `isZero_iff_finrank_eq_zero`.
- `isZero_fibre_iff`: for `t = a(p)` in an affine open `V`, `H^n(Y_t, M_t) = 0` iff the
  corresponding cohomology of the base change of `Y_V → Spec Γ(T, V)` over the residue field of
  `p` vanishes. Both are finite dimensional (Library `properFlatFibreCohomologySemicontinuity`,
  clause 1) of the same dimension (the base-change invariance theorem
  `properFibreCohomologyDimBaseChange`), and the latter is computed on the chosen fibre product
  (Library `nonempty_relativeCohomology_iso_chosenPullback`).
- `surjective_of_sections`: if every fibre over a residue field has a nonzero section, the
  Grassmannian model is surjective (a nonzero `v : Q → κ` has unit ideal of values, so `linePt v`
  is a `κ`-point over `p`).
- `localFibreFlatness : LinearSystemGluing.LocalFibreFlatness`. A universal family over `V` is
  isomorphic over `V` to the Grassmannian model of `exists_model` (`isIso_of_isUniversalOn`). If
  all fibres have `H¹ = 0`, the Čech model is exact at `κ ⊗ K₁` at every maximal ideal
  (`exact_of_isZero_H1`), so `Q` is projective
  (`CokernelDualHom.projective_Q_of_exact`) and the Grassmannian is flat (`Rep.flat_p`) and locally
  of finite presentation (Library `Rep.locallyOfFinitePresentation_p`); surjectivity follows from
  `surjective_of_sections` with the `H⁰` hypothesis.

## Source

Kleiman, *The Picard scheme* (arXiv math/0504020v1), Subsection 3.10 (pp.24–25): (v) implies (i),
so `Q` is locally free and `P(Q)` is flat and locally of finite presentation; the fibre of `P(Q)`
over `t` is nonempty iff `Hom(Q ⊗ κ(t), κ(t)) = H⁰(Y_t, M_t) ≠ 0` by (3.10.1). Kleiman uses this on
p.30, proof of Theorem 4.8.
