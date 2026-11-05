# Torus weight spaces of the Lie algebra

Module `Langlands.GroupScheme.SplitExistence.TorusWeights`, namespace
`Langlands.GroupScheme.SplitExistence.ChevalleyData`. Internal helper of the proof of the split
reductive Existence Theorem (task 2132924b). This is derived content. The Library weight space
`weightSpace t (charOf ξ)` of the Lie algebra consists exactly of the elements whose matrix
(module `LieMatrix`) is a weight matrix of weight `ξ`.

## Declarations

- `torusPointsEquiv_apply_eq_affine`: on an affine test scheme `Spec A`, the characters given
  by global-section coordinates (`torusPointsEquiv`) and by affine coordinates
  (`torusAffineEquiv`) correspond under `affSecEquiv : A ≅ Γ(Spec A)`. This is the Library's
  `Corepresented.pointsEquiv_eq_affinePointsEquiv`.
- `affinePointsEquiv_torusToGL`: in affine coordinates, `torusToGL` sends a point with
  character `χ` to `diag(χ(wt c))`.
- `characterValue_charOf`: the Library value `Lie.characterValue (charOf ξ)` at an affine point
  with character `χ` is `χ(ξ)`.
- `ChevGroup.lieMat_adjoint_torus`: in matrix coordinates, the adjoint action of an affine
  torus point is conjugation by `diag(χ(wt c))`.
- `ChevGroup.mem_weightSpace_t`: a Lie algebra element whose matrix is a weight matrix of
  weight `ξ` lies in `weightSpace G.t (charOf ξ)`, by `IsWeightMatrix.torusHom_conj`.
- `ChevGroup.torusAffineEquiv_id`: the universal affine point of `D(X)`, over `k[X]`, has the
  monomial characters `m ↦ X^m`.
- `ChevGroup.lieMat_weight_eq`: the weight equation for an element of
  `weightSpace G.t (charOf ξ)` at one test point, in matrix coordinates.
- `ChevGroup.torusHom_conj_apply`: entry `(c, d)` of `diag(χ(wt c)) M diag(χ(wt c))⁻¹` is
  `χ(wt c) M_cd χ(-wt d)`.
- `ChevGroup.isWeightMatrix_of_mem_weightSpace`: conversely, the matrix of every element of
  `weightSpace G.t (charOf ξ)` is a weight matrix of weight `ξ`. Evaluate the weight equation
  at the universal point over `k[X]`. Entry `(c, d)` reads
  `X^(wt c - wt d) · M_cd = X^ξ · M_cd` in the group algebra, which forces
  `wt c - wt d = ξ` whenever `M_cd ≠ 0`.
