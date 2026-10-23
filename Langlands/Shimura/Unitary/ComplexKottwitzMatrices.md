# Kottwitz cocharacter matrices on complex test schemes

This module derives the matrices of the actual Kottwitz cocharacter from
`ComplexCocharacter` and `ComplexCocharacterMatrices`. It preserves the
existing convention: conjugate the corrected Harris complex homomorphism
first, then invert its Deligne map. Its provenance is internal: every map
and identity below is constructed from the imported algebra, unit, and
scheme-point comparisons. No matrix formula is an additional premise.

## Diagonal algebra and unit maps

For any commutative ring `S` and natural numbers `n,r`,
`ComplexMatrix.splitDiagonalAlgHom S n r` is the `S`-algebra homomorphism
from `S × S` to the product of two `n × n` matrix algebras whose value at
`(a,b)` is

\[
 (\operatorname{diag}(b\text{ for }i<r;\ a\text{ otherwise}),
  \operatorname{diag}(a\text{ for }i<r;\ b\text{ otherwise})).
\]

The construction takes the appropriate first or second projection at each
index, forms their product homomorphism, and composes with
`Matrix.diagonalAlgHom`. `splitDiagonalAlgHom_apply` identifies this with
the existing `splitDiagonal`. The construction imposes no bound on `r`;
the index test determines the entries even when `r > n` or `n = 0`.

`splitDiagonalUnits` maps a pair of units of `S` to a unit of the product
matrix algebra. It uses `MulEquiv.prodUnits.symm` and the induced map on
units of the algebra homomorphism. Its underlying value is the same pair
of diagonal matrices, as proved by `splitDiagonalUnits_val`. In particular,
inverses throughout the module are inverses of units, not a field inverse
on the possibly non-field ring `S`.

## Conjugation and inversion in split coordinates

For an arbitrary real algebra with involution and a complex homomorphism
`h`, `ComplexHom.conj_deligneAlgebraMap` proves

\[
 h^{\mathrm{conj}}_S(q)=h_S(\operatorname{star}(q)).
\]

Here `q` is an element of `DeligneTorus.Complexification S`; its star
operation fixes the coefficient ring and negates the quadratic imaginary
coordinate. This identity expands the Deligne algebra map as
`q.re ⊗ 1 + q.im ⊗ h(I)` and uses `conj(I) = -I`.

Retain actual `HarrisSignatureCharts C`, a finite `E`-basis `b` of the
algebra, and a commutative complex algebra `S` with compatible real scalar
structure. For a quadratic unit `q`, write `(a,b')` for its image under
`DeligneTorus.splitPointsEquiv S`. Set `rτ = n - 1` at the distinguished
real embedding and `rτ = n` at all other real embeddings.

`conj_delignePoints_matrix` identifies the matrices of the conjugate
homomorphism with `splitDiagonal S n rτ (↑b',↑a)`. The proof applies the
preceding algebra identity, the existing Harris matrix formula, and
`splitEquiv_star`, which exchanges the two coordinates.

`conj_inverse_delignePoints_matrix` identifies the matrices of the inverse
of that similitude with `splitDiagonal S n rτ (↑(b'⁻¹),↑(a⁻¹))`.
Its proof moves inversion through the Deligne point homomorphism and the
split multiplicative equivalence. The first-factor and second-factor
corollaries specialize `q` to the inverse split images of `(u,1)` and
`(1,u)`, obtaining scalar pairs `(1,↑(u⁻¹))` and `(↑(u⁻¹),1)` respectively.
They use cancellation of the split equivalence and the inverse of one.

## Actual scheme-point formula

Retain `D : CentralSimpleUnitaryData E K A n` and compatible signature
charts `C`. These supply the actual central simple CM algebra, second-kind
involution, number-field data, prescribed signatures, and scalar towers.
For every scheme `T` over `Spec ℂ`, every point `x : T → Gm_ℂ`, and every
real embedding `τ`, `kottwitzCocharacter_matrices` computes the coordinates
of

```
x ≫ (D.kottwitzCocharacter C first).hom.hom
```

in the actual iterated complex pullback of the rational group. Write
`S = Γ(T,O_T)` and `u = GroupScheme.Gm.pointsEquiv _ T x`. When
`first = true`, the result is

\[
 (\operatorname{diag}(u^{-1}\text{ for }i<r_\tau;\ 1\text{ otherwise}),
  \operatorname{diag}(1\text{ for }i<r_\tau;\ u^{-1}\text{ otherwise})).
\]

When `first = false`, the two matrices are interchanged. Thus the first
matrix for the first factor has weights minus one on the positive block
and zero on the remaining block. At a non-distinguished embedding the
pair is `(u⁻¹ I, I)`. All off-diagonal entries vanish. No affineness,
reducedness, or finite-type assumption on `T` is needed.

The proof unfolds the existing coordinate function, uses
`kottwitzCocharacter_comparison` to pass to the real algebra model, and
uses `inverseCocharacter_points` to evaluate the inverse map of the
conjugate homomorphism. `factorCocharacter_quadratic` and the two
conjugate-inverse factor formulas then give the result. The real and
complex structures on `S` and their compatibility come from
`ComplexCocharacterMatrices`.

## Scope

This gives the matrix formula for the existing Kottwitz convention and a
reusable diagonal-unit map. The coordinate function still records only
the algebra component, not the scalar multiplier. The module does not
assert a target group-scheme splitting, chart independence or conjugacy,
reflex-field comparison, smoothness, reductivity, or completion of the
PEL geometry, levels, and coefficient descent. Those remain separate
obligations of the surrounding construction.
