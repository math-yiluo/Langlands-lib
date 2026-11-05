# Torus weights on the Lie algebra in matrix coordinates

Module `Langlands.GroupScheme.SplitExistence.LieWeights`, namespace
`Langlands.GroupScheme.SplitExistence.ChevalleyData`. Internal helper of the proof of the split
reductive Existence Theorem (task 2132924b). This is elementary linear algebra combined with
the Library's weight spaces (`weightSpace`) of the adjoint action.

## Declarations

- `IsWeightMatrix ξ N`: every nonzero entry `(c, d)` of the matrix `N` satisfies
  `wt c - wt d = ξ`.
- `IsWeightMatrix.map`: the condition is preserved by any entrywise map sending `0` to `0`.
- `IsWeightMatrix.torusHom_conj`: conjugating a weight matrix of weight `ξ` by the torus
  element `diag(χ(wt c))` multiplies it by `χ(ξ)`. The entry `(c, d)` is multiplied by
  `χ(wt c) χ(wt d)⁻¹ = χ(ξ)`.
- `IsWeightMatrix.diagonalUnits_conj`: conjugation by `diag(s ^ ℓ(wt c))` multiplies it by
  `s ^ ℓ(ξ)`. This is the case `χ = ellChar s` of `torusHom_conj`.
- `torusAffineEquiv A`: the affine points of `D(X)` with values in a `k`-algebra `A`,
  identified with characters `Multiplicative X →* Aˣ` (the Library's
  `Corepresented.affinePointsEquiv` for `Diagonalizable`).
- `ChevGroup.affinePointsEquiv_cochar`: in `GL_n`, the regular cocharacter of `G` is
  `s ↦ diag(s ^ ℓ(wt c))` on affine points. This uses `cochar_comp_i` and the Library's
  `affinePointsEquiv_diagonalCocharacter`.
- `ChevGroup.characterValue_powerHom`: the character `s ↦ s ^ m` of `𝔾ₘ` takes the value
  `s ^ m` on affine points.
- `ChevGroup.mem_weightSpace_cochar`: if the matrix of a Lie algebra element `x` (module
  `LieMatrix`) is a weight matrix of weight `ξ`, then `x` lies in the Library weight space of
  the regular cocharacter `λ` for the weight `ℓ(ξ)`. Over every `k`-algebra `A` and every affine
  point `s` of `𝔾ₘ`, the adjoint action of `λ(s)` is conjugation by `diag(s ^ ℓ(wt c))`, which
  multiplies the matrix by `s ^ ℓ(ξ)`. Injectivity of `lieMat` concludes.
