# Real parameter determinants and central action

The main internal proposition is
`Langlands.Global.RankinSelbergGlobal.RealPlaceAnalyticNonzeroReductionStatement.{u}`:

```text
RealJacquetRestrictionEquationStatement.{u} →
RealStandardKFiniteNonzeroStatement →
RealPlaceFunctionalEquationStatement.{u}.
```

The theorem `realPlaceAnalyticNonzeroReduction` proves this implication with the
field universe `u` free. Both premises are retained. The analytic equation for
actual global restrictions remains open, as does the new purely local
standard-module nonvanishing statement. This conditional reduction does not
prove or complete the unconditional real-place functional equation.

This internal helper calculates the determinant of the explicit tensor block
list `realPairBlocks`. At every real unit `a`, it proves
`determinant(realPairBlocks ds es, a) =
determinant(ds, a)^realRank(es) * determinant(es, a)^realRank(ds)`.

The proof checks the four types of block pairs using the existing tensor
decomposition. The norm of a real unit viewed as a complex unit is its square,
complex conjugation fixes it, and its real sign squares to one. The determinant
formulas for character and induced blocks therefore give the tensor
determinant identity. Two list inductions extend it to presentations.

For the standard module itself, `prod_position_minusOne` computes the product
of its position characters at minus one. A character block contributes its
own character. The two positions of an induced block contribute
`(-1)^(|weight|+1)` and `1`, respectively, whose product is the existing
induced-block determinant at minus one. Equality of the integer and
absolute-integer powers of minus one follows from parity. Induction on the
block list therefore identifies the product with `RealJacquet.determinant`.
Every modulus factor in the principal-series character is one at minus one.
The principal-series covariance law, evaluated at the diagonal matrix with
every entry minus one, proves `RealJacquet.standard_mul_minusOne`.
This applies to every compact-finite standard function, including zero.

The theorem `realMinusOneScalar_eq_parameter_of_nonzero` additionally assumes
one nonzero vector `f` of `realStandardKFinite (r+1) ds` and a parameter
`T.realization.HasRealPlaceParameter v ds`. The parameter supplies an injective
complex-linear map `A` from that standard module into the actual realization,
intertwining compact translations. The source central action and the proved
actual action `realMinusOneScalar_action` give

```text
determinant(ds, -1) • A(f) = realMinusOneScalar T v • A(f).
```

Injectivity gives `A(f) ≠ 0`, so scalar cancellation proves the desired
identity. No surjectivity or identification of a Whittaker model is required
for this comparison.

The remaining local proposition is explicitly

```text
RealStandardKFiniteNonzeroStatement :=
  ∀ ds : List RealBlock,
    ∃ f : realStandardKFinite (realRank ds) ds, f ≠ 0.
```

It concerns exactly the published standard module, with its induced-block
Fourier vanishing conditions, intersected with the compact-finite functions.
It is a statement about local real representations and carries no number-field
or analytic Rankin–Selberg hypotheses. This module does not prove it.
The parameter's injective map alone does not supply this nonzero vector:
injectivity from a zero source would be vacuous.

Assuming that proposition, the rank equality in each parameter transports a
nonzero standard vector to each of the two required ranks. The scalar
comparison for each representation and the tensor determinant identity prove
`realPairCentralCompatibility_of_standardNonzero`. Applying the previous
`realPlaceReflectionReduction` then proves the main implication.

The analytic premise is unchanged: it retains convergence, holomorphy,
meromorphic continuation, both source-convention functional equations for the
actual global restrictions, local-model membership and normalization
identification. These obligations are not consequences of the determinant
calculation. The provenance of this module is internal algebraic derivation
from the published block, standard-module and actual-action definitions; no
new result from the analytic literature is invoked.
