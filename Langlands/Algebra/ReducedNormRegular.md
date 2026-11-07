# Regular norm and the reduced degree

For every finite-dimensional central simple algebra `A` over a field
`K`, every commutative `K`-algebra `R`, and every actual element
`x : R ⊗[K] A`, `Langlands.CentralSimple.norm_eq_reducedNorm_pow`
proves

```text
Algebra.norm R x = reducedNorm K A R x ^ reducedDegree K A.
```

The common universe of `K` and `A` is arbitrary, and the universe of
`R` is arbitrary and independent. Characteristic is unrestricted. No
splitting field or chart is supplied as a hypothesis. `Algebra.norm`
is Mathlib's determinant of the left regular representation on the
whole algebra; `reducedNorm` is the Library's canonical reduced norm,
characterized by determinant after matrix splitting. The formula holds
on all tensor elements, including nonunits and over test algebras with
zero divisors.

This is an internal deduction from the published reduced-norm
construction and Mathlib's determinant, basis, and tensor-product APIs.
It imports `Langlands.Algebra.ReducedNorm` and
`Mathlib.RingTheory.Norm.Basic`. It introduces no new assertion from
external literature.

The proof first establishes
`leftMulMatrix_baseChange_map`. For any finite basis of a ring algebra
over a commutative ring, the matrices of left multiplication in the
base-changed bases commute with any map between commutative scalar
test algebras. Tensor induction reduces this to the basis-coordinate
formula on pure tensors, with additivity handling sums.
`norm_baseChange_naturality` then applies the determinant and its
compatibility with ring maps. These helpers do not require the algebra
to be commutative, simple, central, or over a field; the supplied finite
basis provides the finite free module structure used by the norm.

The helper `norm_matrix` proves, for any square matrix `a` over a
commutative ring with a finite decidable index type `I`,

```text
Algebra.norm R a = a.det ^ Fintype.card I.
```

Its linear equivalence first transposes a matrix and then uses
`Matrix.ofLinearEquiv` to regard it as a family of columns. Conjugating
left multiplication by this equivalence gives the product linear map
that acts by `Matrix.toLin' a` on each column. The commutativity of `R`
identifies the resulting coordinate sums. `LinearMap.det_conj`,
`LinearMap.det_pi`, and `LinearMap.det_toLin'` identify its determinant
with one copy of `a.det` for each column. The explicit equivalence to
the function module also keeps the matrix and function module
structures compatible throughout this determinant calculation.

For the central simple algebra, let `L` be the constructed
`finiteGaloisSplittingField K A` and put `E = L ⊗[K] R`. The actual
scalar inclusion `R →ₐ[K] E` is injective by faithful tensor extension.
Regular-norm naturality and canonical reduced-norm naturality reduce
the desired equality to `E`. The actual extended splitting chart
`Langlands.ReducedNorm.extendSplittingChart` transports the regular
norm to the norm on the matrix algebra. The preceding matrix formula
and the published theorem `reducedNorm_eq_det` prove the equality
there. Injectivity of the scalar inclusion descends it to `R`.

The definition `regularNormUnits` applies `Units.map` to the ordinary
norm on the actual tensor algebra. The theorem
`regularNormUnits_eq_pow` identifies this homomorphism with the
pointwise `reducedDegree K A` power of `reducedNormUnits K A R`.
Extensionality of homomorphisms and of units reduces this to the
proved element formula.

The comparison gives an equality of powers. It does not cancel the
positive exponent to identify two candidate reduced norms, compare
reduced norm with the field norm on a maximal subfield, or prove local
SK₁ vanishing or local Kneser–Tits. Those arithmetic and structural
steps remain separate obligations.
