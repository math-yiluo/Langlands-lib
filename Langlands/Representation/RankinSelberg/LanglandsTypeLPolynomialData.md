# Certified polynomial data for Langlands standard modules

Author: Worker 111.

`Langlands.RankinSelberg.langlandsTypeLPolynomialData` constructs
`LanglandsTypeLPolynomialData` for every pair of genuine tempered Langlands
data of positive ranks. It preserves the original data, canonical topology,
supplied nontrivial unitary additive character, supplied self-dual Haar
measure, independent field and carrier universes, and both rank orders.

The result contains full Whittaker type for the actual standard modules,
an induced polynomial `P` with its existing full symmetric certificate,
every twisted-block polynomial `Q i j` with its existing arbitrary-rank
certificate, and a normalized residual polynomial `D` satisfying

```text
D.coeff 0 = 1
∏ i, ∏ j, Q i j = D * P.
```

This supplies the existence and divisibility portion of
`LanglandsTypeLFactorStatement`. Triviality of `D`, and hence the required
product equality, is a separate remaining obligation.

`analyticTemperedRealTwistWhittakerType` applies the original-action analytic
tempered Whittaker-type adapter. The real determinant-power character has
open kernel. Its value is one on the upper unipotent subgroup, by the
published determinant-norm-one lemma and the inclusion of the norm kernel
in the real-power-character kernel. The full Whittaker-type twist equivalence
therefore supplies full type of the real twist on the original carrier.

`langlandsStandardModuleWhittakerType` destructures the block shape and uses
positivity of every block size to write that size as `m i + 1`.
The block actions, exponents and analytic hypotheses are transported by
this equality. Apply the real-twist helper to each original analytic
tempered block, then `normalizedProductWhittakerType` to the actual
canonical normalized upper induction. Its endpoint is definitionally
the unchanged standard module. No irreducibility of the standard module
is asserted.

For the data constructor, perform the same successor-size conversion on
both shapes and apply
`TemperedLFactorDivisibility.twoFamilyLPolynomialData` to their actual
twisted block families. The two real-twist helper applications discharge
all full-type premises. The resulting symmetric block certificates are
definitionally the required `IsPadicRankLPolynomial` certificates at the
positive successor sizes. Retain the induced and block polynomials, their
full certificates, and the normalized quotient. Classical choice selects
the resulting nonempty data.

The provenance is internal composition of
[the analytic tempered adapter](AnalyticTemperedLFactor.md),
[full Whittaker-type twist transport](WhittakerTypeTwist.md),
[normalized product Whittaker type](NormalizedProductWhittakerTypeProof.md),
[real determinant characters](../Classification/SupercuspidalTwist.md),
[the unipotent determinant norm calculation](TwoBlockDeformationCell.md),
and [finite-family L-divisibility](TemperedLFactorDivisibility.md).
No classification, rationality, genericity or block-polynomial existence
premise is added, and no new external source assertion is used.
