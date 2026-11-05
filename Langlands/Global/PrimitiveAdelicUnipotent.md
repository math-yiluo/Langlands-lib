# Rational reduction of adelic unitriangular matrices

This module shows that the actual adelic upper unitriangular `n × n` matrices
over an arbitrary number field `F` (in universe `u`, every `n : ℕ` including
`n = 0`) are covered by rational unitriangular translates of a single compact
set. In group terms, `N(𝔸_F) = N(F) · Ω_N` with `Ω_N` compact, where `N` is the
upper unitriangular subgroup of `GL(n)`. The adele ring is the full
`Adeles F = AdeleRing (𝓞 F) F` with its actual topology, and rational matrices act
through the entrywise map `algebraMap F (Adeles F)`. Multiplication is on the left:
`μ * N` with `μ` rational.

## Provenance

The statements are derived. Springer, *Reduction theory over global fields*
(1994), registered as `springer-1994-reduction-global-fields`, SHA256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`, uses
compactness of the quotient for a split unipotent group without proving it here.
In Remark 2.2(a) (printed p.212, PDF p.6) the unipotent radical `U` of the minimal
parabolic is `k`-split, and he concludes that there are compact sets
`K' ⊂ G(A)⁰` and `K'' ⊂ U(A)` with `G(A)⁰ = K'.T(c).K''.G(k)`. The proof of
Proposition 2.6 (printed p.213, PDF p.7) uses "`C(U, k)` is compact". His rational
factor acts on the right; here the rational unitriangular matrix multiplies on the
left. This module formalizes no statement of that paper. It proves the special
case of the upper unitriangular group of `GL(n)` directly. The matrix form, the
left multiplication, the column-by-column induction and the box
`unitriangularBox F D` are internal to the project's `GL(n)` Siegel-shape route.
The only analytic input is the Library theorem
`AdelicGroupPoints.exists_isCompact_algebraMap_add_mem`
(module `Langlands.Global.TriangularRationalQuotientCompact`): there is a compact
`D ⊆ 𝔸_F` with `F + D = 𝔸_F`.

## Definitions

* `IsUnitriangular A`, for a square matrix `A` over a commutative ring `R`
  indexed by `Fin n`, means that `A` is upper triangular (`A.IsUpperTriangular`,
  so `A i j = 0` whenever `j < i`) and `A i i = 1` for every `i`.
* `unitriangularBox F D`, for `D : Set (Adeles F)`, is the set of unitriangular
  adelic matrices `M` with `M i j ∈ D` whenever `i < j`.

## Results

* `isUnitriangular_one`: the identity matrix is unitriangular.
* `IsUnitriangular.mul`: products of unitriangular matrices are unitriangular.
* `IsUnitriangular.map`: the entrywise image under a ring homomorphism of a
  unitriangular matrix is unitriangular.
* `IsUnitriangular.det_eq_one`: a unitriangular matrix has determinant `1`.
* `isCompact_unitriangularBox`: if `D` is compact, then
  `unitriangularBox F D` is compact. The box is the product over all entries of
  `D` above the diagonal, `{1}` on the diagonal and `{0}` below it.
* `exists_column_step`: suppose every adele can be moved into `D` by adding a
  rational adele. Let `N` be adelic unitriangular, `μ` rational unitriangular and
  `m` a column index. Then there is a rational unitriangular `μ'` such that
  `μ' * N` and `μ * N` agree in every column `j < m`, and the entries `(μ' * N) i m`
  with `i < m` lie in `D`. The proof is `μ' = μ + E`, where `E` is supported in
  column `m` above the diagonal. Since `N` is unitriangular, `E * N` vanishes in the
  columns before `m` and has entries `r i` in column `m`.
* `exists_unitriangular_mul_mem`: under the same hypothesis on `D`, every adelic
  unitriangular `N` has a rational unitriangular `μ` such that every entry of
  `μ * N` above the diagonal lies in `D`. This is induction on the number of
  columns already reduced, using `exists_column_step`.
* `exists_isCompact_unitriangular_reduction F n`: there is a compact set
  `Ω` of adelic `n × n` matrices, all unitriangular, such that every adelic
  unitriangular `N` has a rational unitriangular `μ` with `μ * N ∈ Ω`. The set
  `Ω` is `unitriangularBox F D` for the compact `D` with `F + D = 𝔸_F` above.

Nothing is asserted about uniqueness of `μ`, about a fundamental domain, about
Haar measure, or about invertible matrices or `GL(n)` as a group. The
determinant lemma is what lets a later unit view these matrices as elements of
`GL(n)`.
