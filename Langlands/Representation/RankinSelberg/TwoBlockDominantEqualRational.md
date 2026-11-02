# Actual equal-rank rational comparison and L clearing

This internal deduction turns `EqualTwoBlockFiniteNumerators` into rational
identities of actual equal-rank integrals and finite clearing of the entire
specified coefficient-model pair. It also gives the intrinsic L-polynomial
divisibility bound for those clearing polynomials. It does not prove either
final dominant-rank gamma or L statement.

`EqualTwoBlockRationalComparison` chooses the same eight scalar/polynomial
witnesses and two integer exponents as the finite-numerator package. Both
`EqualFirstBlockFactorCertificate` propositions remain intact, before all
sections, coefficient functions and row Fourier pairs. The reversed
first-block certificate has original polynomial `P₂D` and dual polynomial
`P₂`, as in the finite-numerator theorem.

For every original section, specified test-model coefficient and row Fourier
pair, the proposition supplies rational continuations `R` and `RD` of the
actual original and reversed-dual equal-rank integrals. The dual functional
is transported through the fixed `reversedDualSectionEquiv`, evaluated at
that equivalence's image of the original section. The test coefficient is
its specified `firstDualModelMap`. With `q` the canonical complex
residue-cardinality unit and

```text
M = clearedProductMultiplierUnit q (ζ₁ ^ t * c₁) d₁ (ζ₂ ^ t * c₂) d₂,
```

the identity is

```text
subst q⁻¹ (laurentToRatFunc ((P₁D * P₂D).toLaurent) * RD)
  = laurentToRatFunc M * laurentToRatFunc ((P₁ * P₂).toLaurent) * R.
```

The polynomial clearing factors and both central-scalar powers remain
present. This is a rational identity, with no cancellation of a nonunit on
bilateral coefficient series.

The same proposition includes `EqualModelFiniteClearing` by `P₁ * P₂` for
every pair of coefficients in the fixed models of `lambda` and `J`, and
every Schwartz–Bruhat row test. For every intrinsic equal-rank L polynomial
`P` of the whole pair, it supplies exactly

```text
∃ (Q : Polynomial ℂ) (e : ℕ), X ^ e * (P₁ * P₂) = Q * P.
```

`equalTwoBlockRationalComparison_of_numerators` implements this implication.
Full Whittaker type of the lower induction follows from its blocks. The
published inverse-transpose and reversed-block theorems give the corresponding
types on the dual side. Nonzero functionals remain nonzero under dualization
and the fixed representation equivalence. `equalRankAnalytic` then supplies
ordinary equal-rank convergence on a right half-plane and rational
continuation for both actual model-integral families. The two half-planes
may differ. `equalRank_hasBilateralSpectralExpansion` applies the published
determinant-slice partition theorem to each convergence result, and
`reflectedNumerators_rationalIdentity` gives the displayed identity.

For uniform model clearing, `modelMap_surjective` realizes every coefficient
in the fixed induced model by a section. `rowFourierCompatibility` supplies
a Schwartz–Bruhat Fourier partner for every row test using the supplied
scalar self-dual measure. The original finite-numerator equation then gives
clearing for that coefficient and test. Both clearing polynomials are
nonzero because they occur in normalized-generator certificates at the
complementary rectangle dimensions. Applying
`equalModelFiniteClearing_polynomialDivisibility` proves the intrinsic
L-polynomial equation. Its intrinsic-to-model argument includes every
functional by full-type scalar multiplicity one; it does not restrict the
intrinsic zeta-value set to a preferred nonzero coefficient.

`exists_equalTwoBlockRationalComparison` discharges the finite-numerator
premise using `exists_equalTwoBlockFiniteNumerators`. Above one common real
opposite-twist bound, it retains absolute convergence of every ordinary
Jacquet section and a nonzero ordinary realizing functional chosen before
the total and two block quotient measures. Every compatible triple then
has the rational comparison and L bound. Its factor witnesses may depend
on that triple.

The construction retains independent field, test and dependent block-carrier
universes. The implication theorem requires full Whittaker type of the test
and blocks, nonzero `lambda` and `J`, compatibility of the total quotient
measure and right invariance of its canonical unipotent Haar measure. The
existence theorem requires nonzero base block functionals, right invariance
also at both block ranks, the supplied nontrivial unitary additive character
and scalar self-dual Haar measure, and compatibility of all three quotient
measures. Reducible full-type representations are allowed.

The provenance is internal: only the imported finite-numerator, analytic,
Fourier-closure, spectral-evaluation and normalized-generator theorems are
combined. No new literature assertion is translated here. Lower-quotient
spectral convergence is not asserted. Identifying the retained block
polynomials with complete symmetric certificates, identifying the rational
gamma product, continuing to the undeformed parameter and handling strict
dominant rank remain separate obligations.
