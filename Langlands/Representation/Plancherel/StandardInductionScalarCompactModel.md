# Compact-model independence of actual canonical standard scalars

## Target and provenance

`Langlands.Plancherel.conditionalStandardInductionScalarCompactModel` proves
`ConditionalStandardInductionScalarCompactModelStatement` at all three
independent universes. This is an internal proof of the exact comparison target
for `StandardInductionCanonicalScalar`, with no new original-source assertion.

## Implemented proof

The actual ambient forward and reverse standard integrals are the same for
both compact subgroups. Transport each first-model whole-operator continuation
to the second model using `transportedCompactModelContinuation`. This retains
its denominator in the actual rational-point character algebra and its whole
regular region. The second-model canonical scalar is independent of its two
continuation choices by the published canonical continuation-independence
result, applied to the second model's two separate nonempty open convergence
subsets. Replace those choices by the transported pair.

Unfold the canonical scalars into their independently selected normalized
compact coefficients (`compactInductionScalarExtraction`). The two relevant
continued composites now have exactly the same open regular region, since the
transported continuations keep the regular regions of `p₀` and `q₀`. This
region is nonempty by `continuedCompositeRegion_nonempty`, from the separate
original open subsets and density of nonzero regular functions. Generic actual
induced irreducibility on the first nonempty open locus `D₀` proves scalarity
of the first composite on this whole regular region
(`continuedInductionComposite_compact_eq_scalar`).

To transfer this identity, fix a regular parameter and let `S` and `T` be the
actual compact-model equivalences `unramifiedCompactModelEquiv` for `P₀` and
`P₁` at the transported character. Write an arbitrary second-model vector as
`S w`, using surjectivity of `S`. The published commuting squares
`transportedCompactModelContinuation_continuedOperator_natural`, applied to the
forward and then the reverse transported continuation, turn the transported
composite applied to `S w` into `S` applied to the first composite at `w`.
Scalarity of the first composite and linearity of `S` show that the transported
composite is the same scalar times the identity. The independently chosen
second-model functional takes the selected vector to one, so
`endomorphismScalarCoefficient_smul_id` extracts the identical scalar. The
open-set uniqueness theorem `ScalarPresentation.toFunctionField_eq_of_eqOn_isOpen`
then identifies the two actual rational function-field elements.

The first irreducibility locus is used for generic scalarity; the second only
selects a normalized coefficient. No intersection of original forward and
reverse convergence regions, no equality of initial continuation choices or
denominators, no containment of compact subgroups and no constant transition
are assumed.

## Scope

This comparison retains the target's actual inducing representation, subgroup,
normalization, measure, character and structural data. Existence of initial
standard-integral convergence and whole-operator rational continuations,
generic induced irreducibility and structural realizations remain explicit
application obligations. No nonvanishing, positivity, source-normalized `j`
or `mu`, broader parabolic/measure independence or Plancherel result is proved.
