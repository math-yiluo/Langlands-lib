# Reduced norm of a finite-dimensional central simple algebra

Let `K : Type u` be a field and `A : Type u` a unital ring with
`[Algebra K A] [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]`.
This module constructs the actual reduced norm on every commutative
`K`-algebra. Its public declarations are in `Langlands.CentralSimple`, and it
imposes no restriction on characteristic or perfectness. The test algebras,
coordinate indices and additional splitting fields may have independent
universes.

The reduced degree is `d = reducedDegree K A`, the natural square root of
`Module.finrank K A`. `reducedNorm_degree_spec` proves `0 < d` and
`Module.finrank K A = d * d`. For every commutative `K`-algebra `R`,

```text
reducedNorm K A R : R ⊗[K] A →*₀ R
```

is an actual multiplicative map with zero. Thus it preserves zero, one and
multiplication. `reducedNorm_naturality` proves compatibility with
`Algebra.TensorProduct.map f (AlgHom.id K A)` for every `f : R →ₐ[K] S`.
The scalar formula is
`reducedNorm K A R (r ⊗ₜ[K] 1) = r ^ d`.
There is no reducedness or nontriviality hypothesis on `R`, and `f` need not
be injective.

For every finite basis `b : Module.Basis J K A`,
`reducedNormPolynomial K A b : MvPolynomial J K` is a genuine coordinate
polynomial. `reducedNorm_eq_polynomialValue` identifies the norm of each
`x : R ⊗[K] A` with evaluation of that polynomial at the coordinates of `x`
in `b.baseChange R`, for every `R`. The polynomial is homogeneous of degree
`d`, is nonzero, and has total degree exactly `d`; the respective theorems
are `reducedNormPolynomial_isHomogeneous`, `reducedNormPolynomial_ne_zero`
and `reducedNormPolynomial_totalDegree`.
`reducedNormPolynomial_basis_independent` states that these evaluations give
the same law for any two finite bases, even with different indexing types.
The argument establishes polynomial identities before evaluation and applies
over finite fields.

The construction supplies its own splitting field and chart through
`Langlands.Algebra.CentralSimple.FiniteGaloisSplitting`.
`finiteGaloisSplittingField K A : Type u` is finite Galois over `K`, and
`finiteGaloisSplittingChart K A` is an actual chart of size `d`.
Those imported constructions first prove preservation of central simplicity
under scalar extension, classify central simple algebras over a separably
closed field, and obtain a chart over `SeparableClosure K`. They then adjoin
the finitely many entries of the images of a finite basis, take their normal
closure inside the separable closure, and descend the chart. The public norm
requires none of these data as an input.

Here is how the determinant law is descended and evaluated. In
`ReducedNormPolynomial`, the determinant of the generic matrix
`∑ j, X j • e (1 ⊗ b j)` is formed over the polynomial ring over a splitting
field. Innerness of full-matrix chart changes proves equality of these
actual polynomials. In `ReducedNormDescent`, twisting a finite Galois chart
by a field automorphism gives another linear chart; chart independence
therefore fixes every polynomial coefficient. The finite Galois fixed-field
theorem puts each coefficient in the image of `K`, yielding
`descendedPolynomial e b`. Injectivity of coefficient extension proves
uniqueness and reflects homogeneity.

`ReducedNormEvaluation` evaluates that descended polynomial in the
base-changed basis. The basis-coordinate expansion proves that, over every
compatible algebra over the splitting field, its value is the determinant
of the scalar-extended chart. To prove zero, one and multiplication over an
arbitrary `R`, it maps `R` injectively into
`finiteGaloisSplittingField K A ⊗[K] R`. This inclusion is injective by
flatness over the field `K`. Naturality and determinant identities there
reflect the required equalities back to `R`. Basis independence and the
scalar formula follow by the same comparison. Evaluation at one over `K`
proves nonvanishing; homogeneous grading then gives the exact total degree.
The definitions in this module use that construction with `Module.finBasis
K A` and the constructed finite Galois chart.

The comparison is universal in the splitting choice. Given any field
extension `L/K` and any chart

```text
e : L ⊗[K] A ≃ₐ[L] Matrix (Fin d) (Fin d) L,
```

`reducedNormPolynomial_map_chart` identifies coefficient extension of the
coordinate polynomial with the determinant polynomial in `e`.
For every commutative `L`-algebra `R` with compatible `K` structure,
`reducedNorm_eq_det` identifies `reducedNorm K A R x` with
`(splittingMap e R x).det`. The map `splittingMap` is the actual extended
chart map; `Langlands.ReducedNorm.extendSplittingChart` packages it as an
algebra equivalence. Its pure-tensor formula is `r` times the coefficient
extension of `e (1 ⊗ a)`. `reducedNorm_eq_chart_det` specializes to
`reducedNorm K A L x = (e x).det`. No finiteness, algebraicity or separability
is assumed for this arbitrary splitting field.

The imported comparison proof extends two charts to a common algebraically
closed overfield, using the algebraicity of the constructed finite Galois
field to embed it there. Chart independence compares their actual
polynomials, and injectivity reflects coefficient equality to `L`. Generic
determinant evaluation then proves the comparison on every further test
algebra, including nonreduced algebras and zero rings.
`reducedNorm_splitting_independent` also states directly that any finite
Galois splitting field, chart and finite basis produce the same map on every
commutative `K`-algebra.

Finally,
`reducedNormUnits K A R : (R ⊗[K] A)ˣ →* Rˣ`
is `Units.map` of the constructed norm, and `reducedNormOne K A R` is
literally its group kernel. `mem_reducedNormOne` identifies membership with
`reducedNorm K A R (x : R ⊗[K] A) = 1`.
`reducedNormUnits_naturality` proves naturality of the group homomorphisms;
its proof applies equality of underlying unit values and norm naturality.

The source is J. S. Milne, *Algebraic Groups*, corrected reprint (2022),
Remark 24.25, printed page 523 (PDF page 534), registered as
`milne-2022-algebraic-groups`, SHA256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The splitting input follows Chapter 24d, Theorem 24.19,
Propositions 24.21–24.22 and the finite Galois step in the proof of
Theorem 24.23, printed pages 521–522 (PDF pages 532–533). Milne's footnote 3
calls the matrix size the reduced degree; his degree is the full dimension.
The complete retained author errata snapshot of 2026-11-04 contains no
correction to these passages.

Milne's convention is determinant after a separable-closure matrix chart,
with inner conjugacy and Galois invariance giving independence and base-field
values. The coefficient descent, arbitrary-test evaluation and common-field
comparison described above are internal derivations of that convention.
The direct-field determinant theorem recovers it, and the polynomial and
all-test theorems establish the stronger law required here. No arbitrary
norm map or record of desired laws is assumed.
