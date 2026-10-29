# Determinant polynomials over arbitrary commutative coefficient rings

This derived module extends the actual endomorphism determinant of
`HodgeDeterminant` to the coefficient rings needed for Lie sections.
It proves basis independence over every commutative ring, including
finite rings, rings with nilpotents, and the zero ring. It constructs
coefficient change and identifies it with the determinant polynomial
of the actual tensor-extended endomorphisms. No polynomial-function
argument, infinitude hypothesis or reducedness hypothesis is used.

All declarations are in `Langlands.Shimura.HodgeDeterminant`.
The starting data are a commutative ring `R : Type u`, an additive
commutative group `M : Type v` with an `R`-module structure, a finite
family `f : ι → Module.End R M` with `ι : Type w`, and a finite basis
`b : Module.Basis κ R M` with `κ : Type t` and decidable equality.
A second finite basis can have a different index type in `Type s`
or, where the coefficient ring already uses `s`, in `Type r`.
No nontriviality of the rings or nonemptiness of the index types is
assumed. The source module and each basis are actual modules and bases;
there is no determinant supplied as an input.

`matrix_eq_sum` rewrites the existing universal matrix as

```text
Σ i, X i • map C (toMatrix b b (f i)).
```

For another finite basis `b'`, `matrix_changeBasis` proves that its
universal matrix is

```text
map C (b'.toMatrix b) * matrix b f * map C (b.toMatrix b').
```

The two constant transition matrices are inverses, even when their
index types differ. The implemented proof distributes matrix products
through the finite family sum, moves each variable scalar outside,
and maps the ordinary change-of-basis identity into the polynomial
ring. `polynomial_basis_independent_commRing` takes determinants and
uses Mathlib's `Matrix.det_conj_of_mul_eq_one`, together with both
transition-matrix inverse identities. This supplies arbitrary-ring
basis independence alongside the earlier infinite-domain theorem,
without editing that published theorem. Mathlib's determinant lemma
also handles the zero ring, where different basis cardinalities can
occur and all coefficient values coincide.

For any `S : Type s` with `CommRing S` and ring homomorphism
`g : R →+* S`, `mappedPolynomial g b f` is coefficientwise
`MvPolynomial.map g (polynomial b f)`. Its basis-independence theorem
follows from the preceding polynomial equality. `coeff_mappedPolynomial`
gives the coefficient formula; `mappedPolynomial_id` gives the
identity law; `map_mappedPolynomial` gives the law for a further map
`h : S →+* T`, with `T : Type r`, using `h.comp g` in that order.
`mappedPolynomial_isHomogeneous` preserves the degree `card κ`.
This is homogeneous-support membership and includes zero polynomials;
it does not assert nonzero total degree.

When `S` additionally has an `R`-algebra structure,
`mappedPolynomial_eq_baseChange` identifies mapping along
`algebraMap R S` with the determinant polynomial on `S ⊗[R] M`,
using `Algebra.TensorProduct.basis S b` and the actual linear maps
`(f i).baseChange S`. Its proof uses the matrix formula
`LinearMap.toMatrix_baseChange`, coefficient-map compatibility with
finite sums and variables, and compatibility with determinants.
`mappedPolynomial_eq_baseChange_basis` permits any finite `S`-basis
of that same tensor module, possibly with a different index type.
Finally, `eval_mappedPolynomial_baseChange` identifies evaluation at
`x : ι → S` with

```text
LinearMap.det (Σ i, x i • (f i).baseChange S).
```

Thus this is a statement about the actual endomorphisms on the scalar
extension, in addition to a formal coefficient-map identity.

This is internal algebraic infrastructure derived from the published
`HodgeDeterminant` construction and the pinned Mathlib transition-matrix,
determinant and tensor-basis lemmas. It introduces no new assertion
from the literature. The motivation is the subsequent comparison of
Kottwitz's Hodge determinant with determinants on actual Lie sections;
constructing those section actions, restriction compatibilities and
the arithmetic comparison remains further work. No integral coefficient
claim or moduli scheme is constructed here. Worker 57 authored this
extension and its implemented proofs.
