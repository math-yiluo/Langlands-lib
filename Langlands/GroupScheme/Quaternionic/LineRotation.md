# Rotations of a nondegenerate quaternionic line

Module `Langlands.GroupScheme.Quaternionic.LineRotation`, namespace
`Langlands.GroupScheme.Quaternionic.FirstKindInvolution`.

## Setting

`D` is a division algebra over a field `F` with a first-kind involution `σ`,
`q : σ.QuadraticForms (Fin n)` has polar Gram matrix `P = σ.polar q` and hermitian form
`h(v, w) = σ.sesqForm P v w = ∑ v_j P_{jk} σ(w_k)`. Write `c = h(x, x)` for a row vector
`x ∈ Dⁿ`. When `c ≠ 0`, the line `D x` is nondegenerate. Over a commutative `F`-algebra `R`,
`ι : D → R ⊗ D` is the inclusion `d ↦ 1 ⊗ d` and `σ_R = σ.baseChange R`.

For `c ≠ 0`, the map `v ↦ v - h(v, x) c⁻¹ (1 - t) x` over `R ⊗ D` sends `a x` to
`a t x` because `h(a x, x) = a c`. It fixes every `v` with `h(v, x) = 0`. The condition
`t ι(c) σ_R(t) = ι(c)` makes it an isometry of the extended form. When the reduced norm
is defined, `Nrd(t) = 1` makes the rotation have reduced norm one.

## Matrices

* `lineColumn σ q x R` is the column `ι(P σ(x))`, `lineRow σ q x R t` the row
  `ι(c⁻¹)(1 - t) ι(x)`, and `lineRotationMatrix σ q x R t = 1 - vecMulVec (lineColumn)
  (lineRow t)`, the matrix of the rotation above on row vectors over `R ⊗ D`.
* `lineRow_dotProduct_lineColumn`: `lineRow t ⬝ lineColumn = ι(c⁻¹)(1 - t) ι(c)`.
* `lineRotationMatrix_mul` (for `c ≠ 0`): `M(s) M(t) = M(st)`; `lineRotationMatrix_one`:
  `M(1) = 1`. The proof expands the product of two rank-one corrections
  (`vecMulVec_mul_vecMulVec'`) and uses the dot product above.
* `lineRotationMatrix_polar` (for `c ≠ 0`): if `t ι(c) σ_R(t) = ι(c)` then
  `M(t) · P · σ_R(M(t))ᵀ = P`, with `P` mapped by `ι`. The proof
  expands both rank-one corrections and reduces to the identity
  `c⁻¹(1 - t) + (1 - σ_R t)c⁻¹ = c⁻¹(1 - t) c (1 - σ_R t) c⁻¹`, which follows from
  `t c σ_R(t) = c` and `σ(c⁻¹) = c⁻¹` (`map_sesqForm_polar_self_inv`).
* `matrixReducedNorm_lineRotationMatrix` (for `D` central, finite dimensional, `n ≠ 0`,
  `c ≠ 0`): the reduced norm of `M(t)` is `Nrd(t)`. By
  `matrixReducedNorm_one_sub_vecMulVec`, `Nrd(1 - a b) = Nrd(1 - b·a)`, and
  `1 - ι(c⁻¹)(1 - t)ι(c) = ι(c⁻¹) t ι(c)`.
* `map_lineRotationMatrix`: coefficient changes `f : R →ₐ[F] S` act entrywise,
  `M_R(t).map (f ⊗ id) = M_S((f ⊗ id) t)`.
* `lineReflection σ q x = 1 - vecMulVec (P σ(x)) (c⁻¹ · 2 · x)` is a matrix over `D`. For
  `c ≠ 0` it negates the line `D x` and fixes its orthogonal complement.
  `map_lineReflection` identifies its image over `R ⊗ D` with `M(-1)`.
* `lineRotationMatrix_neg_one_ne_one` (over a field `K` of characteristic zero, `c ≠ 0`):
  `M(-1) ≠ 1`. Otherwise the rank-one correction `vecMulVec (lineColumn) (lineRow (-1))`
  vanishes, which forces `x = 0`, contradicting `c ≠ 0`.
* The auxiliary identities `vecMulVec_mul'`, `mul_vecMulVec'` (products of a rank-one matrix
  with a matrix) and `baseChange_includeRight` (`σ_R(ι y) = ι(σ y)`).

## Points

Assume now that `F` has characteristic zero, `D` is central and finite dimensional, and
`n ≠ 0`.

* `lineTorus σ q x R` is the subgroup of `(R ⊗ D)ˣ` of units `t` with
  `t ι(c) σ_R(t) = ι(c)` and `Nrd(t) = 1`; `mem_lineTorus_iff` unfolds membership.
* `lineRotationUnit σ q x R hc t` (for `hc : c ≠ 0`) is the unit of
  `R ⊗ M_n(D)` corresponding to `M(t)` under `coefficientEquiv` (its inverse corresponds to
  `M(t⁻¹)`), with `coefficientEquiv_lineRotationUnit` and the multiplicativity
  `lineRotationUnit_mul`.
* For `t ∈ σ.lineTorus q x R`, `lineRotationUnit_mem_isometry` places this unit in
  `σ.tensorIsometryGroup q R` (from `lineRotationMatrix_polar`, writing the polar matrix as
  `out q + σ(out q)ᵀ`), and `reducedNorm_lineRotationUnit` shows its reduced norm is `1`
  (from `matrixReducedNorm_lineRotationMatrix`).
* `lineRotationTensorHom` is the resulting group homomorphism from `lineTorus` to
  `σ.tensorNormOneIsometryGroup q R`, and `lineRotationHom σ q x R hc` its composite with
  `normOneIsometryAffinePointsEquiv`, a homomorphism to the affine `R`-points of the group
  scheme `σ.normOneIsometryGroup q`. `lineRotationHom_val` identifies the tensor unit of
  `lineRotationHom t` with `lineRotationUnit t`.
* `lineTorusMap σ q x f` is the homomorphism between the `lineTorus` subgroups induced by
  a coefficient change `f : R →ₐ[F] S`, and `lineRotationHom_naturality` states
  `affinePointMap f (lineRotationHom_R t) = lineRotationHom_S (lineTorusMap f t)`. Its proof
  compares tensor units via `FiniteAlgebraUnits.affinePointsEquiv_naturality` and
  `map_lineRotationMatrix`.

## Provenance

The formulas for rotations of a nondegenerate line fixing its orthogonal complement
follow from the definition of `σ.sesqForm` and the description of the points of
`σ.normOneIsometryGroup q` in `Quaternionic/NormOneIsometryAffinePoints`.
