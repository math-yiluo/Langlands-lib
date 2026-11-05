# Diagonalizing an upper triangular cocharacter by an upper triangular matrix

This internal unit refines the published diagonalization of cocharacters of `GL_n`
(`Dynamic.GeneralLinearCocharacterDiagonal`). Here the cocharacter is upper triangular, and the
conjugating matrix is required to be upper triangular too. Upper triangular means lying in
`blockParabolicSubgroup` or `blockParabolic` for the weights `i ↦ -(i.val : ℤ)` on `Fin N`.

## Main theorem

`GeneralLinear.exists_triangular_innerIso_comp_eq_diagonalCocharacter` works over a field
`k : Type u`. Let `χ : 𝔾_m ⟶ GL_N` be a homomorphism of group schemes over `Spec k`. Assume
that for every test scheme `T` and every point `t` of `𝔾_m` over `T`, the point `t ≫ χ` lies in
the block parabolic subgroup functor `blockParabolic (Fin N) k (fun i => -i)`. It constructs a
`k`-point `g` of `GL_N` in that subgroup functor and weights `e : Fin N → ℤ` with
`χ ≫ (innerIso g).hom = diagonalCocharacter (Fin N) k e`. This is an equality of
group-scheme morphisms, so it holds on every test scheme.

## Proof

* `CocharacterDiagonal.exists_triangular_diagonalizingMatrix` is the matrix step. Take a
  representation `ρ` of the split torus on `Fin N` whose universal matrix `U` is upper
  triangular. Its entries lie in the group algebra `k[I → ℤ]`. Since `U` is invertible and upper
  triangular, each diagonal entry `U j j` is a unit, hence nonzero. Choose an exponent `m j`
  with nonzero coefficient in `U j j`. Let `M` be the matrix whose `j`-th column is the published
  coefficient column `coefficientColumn I ρ (m j) j`, the `m j`-coefficients of the `j`-th
  column of `U`. Below the diagonal these coefficients vanish because `U` is upper triangular,
  and on the diagonal they are nonzero. So `M` is upper triangular with nonzero determinant, and
  it defines `B : GL (Fin N) k`. By the published `coefficientColumn_weight`, every column of
  `M` is a weight vector after every coefficient extension. Hence
  `B⁻¹ · matrixAt t · B` is diagonal on every commutative `k`-algebra, as in the published
  `exists_diagonalizingMatrix`.
* `CocharacterDiagonal.affinePointsEquiv_apply_eq_zero`: a matrix entry of a point of `GL_n`
  over an affine test vanishes when the corresponding entry of its global-section matrix
  vanishes. This uses `pointsEquiv_eq_affinePointsEquiv` and the inverse of the published
  sections isomorphism.
* `CocharacterDiagonal.rationalMatrixPoint_mem_blockParabolic`: the published rational point
  attached to a matrix of `blockParabolicSubgroup R e` lies in `blockParabolic n R e`. This
  uses `pointsEquiv_naturality` and `pointsEquiv_eq_affinePointsEquiv`.
* For the main theorem, restrict `χ` along the published rank-one torus comparison `gmIso`.
  The universal matrix of the result is the affine matrix of a point `t ≫ χ`. By hypothesis and
  `affinePointsEquiv_apply_eq_zero` it is upper triangular, so the matrix step gives `B`. The
  point `g` is `rationalMatrixPoint B⁻¹`. It is upper triangular because the block parabolic
  subgroup is closed under inverses. The equality with the diagonal cocharacter is checked at
  the universal point of `𝔾_m`, exactly as in the published
  `exists_innerIso_comp_eq_diagonalCocharacter`.

## Provenance

Internal. The argument reuses the coefficient-column method of the published unit
`Dynamic.GeneralLinearCocharacterDiagonal`, authored by Worker 74, and replaces its basis
selection by an explicit choice of one coefficient column per index. No perfectness,
characteristic or algebraic-closure hypothesis is used.
