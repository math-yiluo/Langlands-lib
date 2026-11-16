# Canonical p-adic specialization of general local-field data

This is an internal comparison construction, derived from the Library's
`PadicField.TopologicalData`, `LocalFieldData`, and the published general
normalization comparison. It introduces no new mathematical hypothesis,
typeclass, additive character or Haar measure.

## Construction and use

`Langlands.PadicField.TopologicalData.toLocalFieldData` projects the topology,
valuation and local-field certificate of any supplied p-adic topological data
to `LocalFieldData`. It forgets the extra base-extension data. Its residue
field, residue cardinality, discrete valuation, chosen uniformizer, order
and residue-normalized absolute value are definitionally the existing
supplied p-adic objects. The comparison lemmas are proved by reflexivity.

`F.canonicalLocalFieldData` applies that construction to
`F.canonicalTopologicalData`. A consumer that needs the canonical p-adic
specialization imports `Langlands.LocalField.PadicBridge` and writes
`open scoped Langlands.PadicField.CanonicalLocalField`. This single scope
supplies the canonical topology and valuation, their nonarchimedean
local-field certificate, the p-adic valuative extension and module-topology
certificates, Hausdorffness, total disconnectedness, and the Borel measurable
space and its certificate. The instances are scoped so a consumer can opt
into this choice in one place. General-field theorems keep their ambient
instances and do not need this scope.

Hausdorffness reuses
`HarmonicAnalysis.GeneralLocalField.t2Space`; total disconnectedness uses
the Hausdorff nonarchimedean ring structure, as in the published all-field
lattice-geometry proof. The canonical data agree definitionally with
`LocalFieldData.ofInstances F.Carrier` under these instances.

## The explicit interface of the general JPSS statements

The published statements
`Langlands.RankinSelberg.LocalFieldUnequalRankFunctionalEquationStatement`,
`LocalFieldPrincipalSeriesGammaMultiplicativityStatement` and
`LocalFieldPrincipalSeriesLFactorMultiplicativityStatement` take a field of
any characteristic with a valuation, topology and
`IsNonarchimedeanLocalField` certificate. They use the existing generic
representations, Whittaker functionals, zeta values and local-factor
relations. They expose the following data and hypotheses:

- A natural number `q` with
  `Conductor.UnramifiedPrincipalSeries.IsResidueCardinality q`, meaning
  equality with the cardinality of the actual valuation residue field.
  The unequal-rank statement writes this equality directly.
- A real absolute value `abv`, a unit `ϖ` satisfying
  `GeneralLinear.Iwasawa.IsUniformizingElement`, and the laws
  `abv ϖ = (q : ℝ)⁻¹` and `abv x = 1` when the valuation of `x` is one.
- Borel measurable spaces, an additive Haar measure `ν` and a nontrivial
  unitary additive character `ψ`, with `HarmonicAnalysis.IsSelfDual ψ ν`
  when required by the functional equation or gamma normalization.
- For the unequal-rank equation, a quotient measure satisfying
  `QuotientIntegration.IsCompatible`.

Related conductor and spherical interfaces also take a general-linear
Haar measure with `Conductor.IsJacquetNormalization`. This is the existing
predicate on that measure; the two principal-series statements above use
the measure conventions already present in their general pair-factor
relations.

`canonical_isResidueCardinality` supplies the first predicate from the
canonical p-adic data. `eq_canonical_residueCardinality` identifies any
explicit `q` satisfying it.
`eq_canonical_normalizedAbsoluteValue` is a specialization of the published
`AllField.RankinSelberg.eq_normalizedAbsoluteValue_ofInstances`.
`explicit_abv_eq_canonical_normalizedAbs` gives its pointwise form.
Thus the explicit absolute value is the residue normalization of the
canonical data; the base-extending spectral norm is not substituted for it.
The uniformizer need not be the chosen `canonicalLocalFieldData.uniformizer`.

The measures and character remain explicit inputs. No measure is chosen,
rescaled or transported by this construction. In particular self-duality
and Jacquet normalization remain precisely the existing predicates on
the consumer's actual measures.

## Provenance

This module packages and compares existing Library data. The arithmetic
definitions are in `LocalField/Normalization/Definitions`,
`LocalField/LocalFieldData`, and `LocalField/PadicResidueNormalization`;
the comparison theorem used for explicit inputs is in
`AllField/Representation/RankinSelberg/LocalFieldUnequalRankFunctionalEquationReduction`.
Its proof is reused without modification. The mathematical JPSS statements
and their source correspondence remain those documented in their own paired
Markdown files. This module asserts no additional JPSS theorem.
