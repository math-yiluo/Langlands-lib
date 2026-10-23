# Full split points of the actual Kottwitz cocharacter

This module combines the matrix formulas of `ComplexKottwitzMatrices` with the
full multiplicative point equivalence of `ComplexGroupPoints`. It constructs
an explicit family of matrix units together with a scalar unit and proves
that it is the image of the actual Kottwitz cocharacter point. Its provenance
is internal: the coordinate formulas and inverse map are derived from these
imported constructions and the multiplier formula in `ComplexCocharacter`.

## Explicit split point

Let `S` be any commutative ring, `n` a natural number, `I` an index type and
`distinguished : I`. Put `rτ = n - 1` at the distinguished index and `n`
elsewhere. For `u : Sˣ`,
`ComplexMatrix.kottwitzSplitPoint S n I distinguished first u` belongs to

\[
 \left(\prod_{\tau\in I}\mathrm{GL}_n(S)\right)\times S^\times,
\]

where `GL_n(S)` here means units of the matrix algebra, without a scheme
interpretation. For `first = true`, its matrix at `τ` is

\[
 \operatorname{diag}(u^{-1}\text{ for }j<r_\tau;1\text{ otherwise});
\]

for `first = false`, it is

\[
 \operatorname{diag}(1\text{ for }j<r_\tau;u^{-1}\text{ otherwise}).
\]

In both cases its scalar component is `u⁻¹`. The matrix unit is constructed
by applying `splitDiagonalUnits` to `(1,u⁻¹)` or `(u⁻¹,1)` and taking the
first component of `MulEquiv.prodUnits`. This supplies its inverse and both
unit identities, rather than merely specifying an invertible matrix value.
`kottwitzSplitPoint_matrix` proves the displayed matrix formula using
`splitDiagonalUnits_val`; `kottwitzSplitPoint_multiplier` is definitional.
The construction includes arbitrary index types and `n = 0`, and assumes
neither nontriviality nor a field structure on `S`.

## Actual complex scheme points

Retain `D : CentralSimpleUnitaryData E K A n`, the compatible scalar towers,
and `C : HarrisSignatureCharts D.toSecondKindInvolution n Φ` used by the
existing actual complex cocharacter. For any scheme `T` over `Spec ℂ`, write
`S = AlgebraInvolution.complexTestAlgebra T`, whose underlying ring is
`Γ(T,O_T)`. Let `x : T → Gm_ℂ` and let
`u = GroupScheme.Gm.pointsEquiv _ T x` be the associated scalar unit.

`kottwitzCocharacter_split_multiplier` proves that the scalar component of

```
D.complexGroupPointsEquiv C T
  (x ≫ (D.kottwitzCocharacter C first).hom.hom)
```

is `u⁻¹`. The proof uses `complexGroupPointsEquiv_multiplier` and
`kottwitzCocharacter_comparison` to pass to the actual scalar-extended
algebra model, then applies the inverse-cocharacter multiplier formula for
`(D.realComplexHom C).conj`. Thus it retains conjugation before inversion.

`kottwitzCocharacter_split_points` proves the equality of the full split
point above with

```
ComplexMatrix.kottwitzSplitPoint S n (E →+* ℝ)
  C.distinguished first u
```

for both choices of the source factor. The proof compares the two product
components. For the matrix-unit family it uses extensionality of functions
and units, `complexGroupPointsEquiv_matrix`, the actual
`kottwitzCocharacter_matrices` formula, and the explicit split matrix formula.
The scalar component is the preceding multiplier theorem. Equality therefore
holds in the full product group, not just after forgetting invertibility or
the scalar component.

Finally, `kottwitzCocharacter_points_of_split` reconstructs the original
scheme point: applying `(D.complexGroupPointsEquiv C T).symm` to the explicit
split point gives

```
(GroupScheme.Gm.pointsEquiv _ T).symm u ≫
  (D.kottwitzCocharacter C first).hom.hom
```

The proof uses injectivity of the full point equivalence and its inverse
identities together with the forward formula. All three comparisons include
nonaffine, nonreduced and empty test schemes and require no nontriviality of
the section ring.

The target is the existing product of matrix-unit groups and scalar units.
This module does not construct the general linear group scheme, a scheme
splitting, or a classification of cocharacter conjugacy classes. Those remain
separate steps in the Harris geometry construction.
