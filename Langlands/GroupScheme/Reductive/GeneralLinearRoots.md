# The roots of the diagonal torus of `GL_n`

Worker 274.

This is a helper module for the proof of `GeneralLinearRootDatumStatement`. It proves
`roots_diagonalTorus`: over a field `k`, the roots of the diagonal torus of
`GL_n` are the characters `χ` with
`characterLatticeEquiv χ = e_{⟨i⟩} − e_{⟨j⟩}` for some `i ≠ j` (Milne, Example
21.6, printed p.426, PDF 442: `T` acts on `E_ij` through `χ_i − χ_j`). The weight
spaces are those of the actual adjoint representation over all test algebras
(module `Langlands.GroupScheme.Torus.Weights`); this all-test-algebra
formulation over an arbitrary field is derived, Milne computing the conjugation
action on `gl_n` directly. The proof computes them with the
matrix coordinates of the Lie kernel of `GL_n` from Worker 339's module
`Langlands.GroupScheme.Lie.GeneralLinearAdjoint`: the linear coordinates
`DualNumber.pointKernelLinearEquiv`, their naturality, and the conjugation
formula `DualNumber.adjoint_pointKernelLinearEquiv`.

## Coordinates of affine torus points

- `torusCoords t` gives the coordinates, as units of `A`, of an `A`-point of the
  split torus, through the published `splitTorus.affinePointsEquiv`.
  `affineTorusPoint v` is the point with coordinates `v`
  (`torusCoords_affineTorusPoint`).
- `affinePointsEquiv_comp_diagonalTorus`: the matrix of the image of `t` in
  `GL_n(A)` is `diag(torusCoords t)`. The entries are computed in global
  sections and transported through the published `affineSectionsIso`.
- `characterValue_characterLatticeEquiv_symm`: the character with coordinates
  `m` takes the value `∏ τ_c^{m_c}` at `t`, where `τ = torusCoords t`.

## Weight spaces

`mem_weightSpace_diagonalTorus_iff` characterizes membership of the element
with matrix `Y` in `weightSpace (diagonalTorus n k) χ`: for every algebra `A`,
every `A`-point `t` and all `a, b`, the identity
`τ_a · Y_ab · τ_b⁻¹ = χ(t) · Y_ab` holds in `A`. This follows from naturality of
the linear coordinates, the conjugation formula for `adjoint`, and the
injectivity of the coordinates.

## Roots

- `single_mem_weightSpace i j`: the matrix unit `E_ij` lies in the weight space
  of the character with coordinates `e_i − e_j`, because
  `∏ τ_c^{(e_i − e_j)_c} = τ_i τ_j⁻¹` (`prod_zpow_single_sub`).
- `roots_diagonalTorus`, `⊇`: for `i ≠ j` this character is nonzero, and the
  weight space contains `E_ij ≠ 0`.
- `roots_diagonalTorus`, `⊆`: a nonzero element of a weight space has a
  nonzero entry `Y_ab`. For each `c`, test with the `k[T, T⁻¹]`-point with
  coordinates `(1, …, T, …, 1)` at position `c`
  (`val_mulSingle_coordUnit`, `val_inv_mulSingle_coordUnit`,
  `prod_mulSingle_zpow`). This gives
  `C(Y_ab) T^{[a = c] − [b = c]} = T^{m_c} C(Y_ab)`, so
  `m_c = [a = c] − [b = c]` by `exponent_eq_of_C_mul_T`. Hence
  `m = e_a − e_b`, and `a ≠ b` because the character is nonzero.
