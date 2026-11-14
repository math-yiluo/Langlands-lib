# The ideal of the zero locus of a regular section is the dual line bundle

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.SectionZeroIdeal`.

- Coordinates of a trivialization through the Library's `trivGen`/`trivDualGen`
  (`Picard/LineBundleDualEvaluation`): `dualGen`, `coord`, `coordEquiv`, `dualCoordEquiv`,
  `eval_smul_comm`, `dual_eq_smul`, and the basis of opens `FrameOpen`.
- `evalHom σ : L^∨ ⟶ kernelModule (zeroIdeal L σ).subschemeι`, evaluation at `σ`, built on the
  basis of frame opens with the Library's `BasisHomGluing.exists_hom_of_basis`.
- `isIso_evalHom`: for a regular section it is an isomorphism (bijective on a basis of opens;
  Library `ProperFormalCoherentExistenceOfFLT.isIso_of_bijective_of_basis`).
- `isEffectiveCartierIdeal_zeroIdeal`: the zero ideal of a regular section is an effective
  Cartier ideal (Library `IsEffectiveCartierIdeal`).
- `nonempty_lineBundle_zeroIdeal_iso`: `O(D_σ) ≅ L` for the zero locus `D_σ`, where `O(D)` is the
  Library's `EffectiveCartierDivisor.lineBundle` (the dual of the ideal line bundle).
- `zeroIdeal_canonicalSection`: for every effective Cartier divisor `D`, the zero ideal of the
  Library's canonical section of `O(D)` is the ideal of `D`.

## Source

Kleiman, *The Picard scheme*, p.25, proof of Theorem 3.13 and Exercise 3.14: a regular section of
`L` defines a divisor `D` with `O(D) ≅ L`, and a divisor is the zero scheme of the canonical section
of `O(D)`.
