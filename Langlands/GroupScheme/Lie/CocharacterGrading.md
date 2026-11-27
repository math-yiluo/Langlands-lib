# The tangent grading defined by a cocharacter

The module `Langlands.GroupScheme.Lie.CocharacterGrading` relates the weight decomposition of the
Lie algebra of an affine group `G` over a field `k` under a cocharacter `χ : Gm → G` (adjoint
action) to the eigenspaces of the inner derivation by the tangent vector `dχ(1)`.

## Main results

- `characterValue_powerHom_gmInfinitesimal`: the `n`-th power character of `Gm` takes the value
  `1 + n ε` at the tangent point `1 + ε` of `Gm(k[ε])`.
- `cocharacterLieVector χ`: the tangent vector `dχ(1)`, the image under `χ` of the tangent point
  `1 + ε`.
- `lie_cocharacterLieVector_of_mem_weightSpace`: on the weight space of the `n`-th power character,
  `⁅dχ(1), X⁆ = n • X`. The weight condition at the dual-number point `1 + ε` says that
  `Ad(χ(1 + ε)) X = (1 + n ε) X`; reading off the `ε`-coefficient with the Library's adjoint
  representation in finite coordinates (`adjointRepresentation`,
  `adjointDifferentialLieHom_apply_bracket`) gives the bracket.
- `iSup_weightSpace_powerHom_eq_top`: the weight spaces of the power characters span the Lie
  algebra (`isInternal_weightSpace_of_isSplitTorus` for the split torus `Gm`, every character of
  `Gm` being a power character).
- `mem_weightSpace_powerHom_iff`: in characteristic zero, the weight space of the `n`-th power
  character is exactly the `n`-eigenspace of `ad dχ(1)`. The weight spaces span, `ad dχ(1)` acts on
  them by the pairwise distinct scalars `n`, so each weight space is the whole eigenspace
  (`Langlands.Algebra.BaseChangeEigenvectors.eq_eigenspace_of_iSup_eq_top`).

The brackets are those of the scoped instances of `Langlands.GroupScheme.Lie.FieldAlgebraLie`.

## Sources

This is the standard description of the grading of the Lie algebra by a cocharacter (A. Borel,
*Linear Algebraic Groups*, 2nd ed., §III.8; T. A. Springer, *Linear Algebraic Groups*, 2nd ed.,
§3.2 and §4.4).
