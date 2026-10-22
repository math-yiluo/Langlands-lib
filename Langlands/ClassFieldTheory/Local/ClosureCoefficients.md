# Coefficient inclusion from an actual intermediate field

Author: Worker 42.

`continuous_unitAction` first proves joint continuity of the actual
automorphism action on discrete units of an algebraic field extension.
It uses the explicit open unit stabilizers from `Cohomology` and Mathlib's
equivalence between joint continuity on a discrete space and openness
of every stabilizer. It does not infer joint continuity from continuity
of individual operators. This certificate applies in particular to
algebraic-closure units, with independent base and extension universes.

`continuousToRelative K L n` specializes the published canonical
`Langlands.Continuous.continuousToOrdinary` map to these same discrete
unit coefficients. Its source is actual continuous cohomology and its
target is the ordinary `relativeCohomology K L n`; its action is unchanged.
It is defined in every natural degree with independent base and extension
universes. Invertibility is neither asserted nor assumed. This forward
map permits an invariant compatibility diagram to be formulated on
continuous representatives. The inverse finite-group comparison is
constructed separately in [FiniteComparison](FiniteComparison.md).

Let `E` be a normal intermediate field of `AlgebraicClosure K / K`.
`closureRestriction` is the actual restriction homomorphism from
`Field.absoluteGaloisGroup K` to `Gal(E/K)`, with the Krull topologies.
Its continuity is Mathlib's proved `restrictNormalHom_continuous`.
No abstract group or supplied quotient homomorphism is substituted.

`closureInflationCoefficients` includes actual units of `E` into actual
units of the algebraic closure. It uses the same explicitly lifted integer
ring and the discrete coefficient topologies as `Cohomology`. Linearity
comes from `unitInclusionLinear`; continuity follows from the discrete
source. Equivariance is proved using restriction of the very same algebra
automorphism, via `AlgEquiv.restrictNormal_commutes`.

`closureContinuousInflation` applies Mathlib's genuine continuous
cohomology functorial map to that continuous group map and coefficient
morphism, in every natural degree. Its source is **continuous**
cohomology of `Gal(E/K)`, not ordinary `relativeCohomology K E`.
When `E/K` is finite, the Krull topology on `Gal(E/K)` is discrete by
Mathlib's existing instance. [FiniteComparison](FiniteComparison.md)
constructs the ordinary-to-continuous finite-group comparison and composes
it with this map to define `closureInflation` on ordinary relative
cohomology. This file does not assume that comparison or identify the two
groups by definition.

The field and its actual intermediate fields retain arbitrary universe
`u`, with no resizing. Normality is the condition that makes restriction
land in automorphisms of `E`; finiteness is not needed for this map
itself. No local-field, invariant, class-formation, or reciprocity
conclusion is an input.

## Source and dependency correspondence

Jean-Pierre Serre, *Local Fields*, English translation, GTM 67, 1979,
registered source `serre-1979-local-fields`, retained at
`C:/Central-Library/Serre--Local Fields--1979.pdf`,
SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Chapter X, section 3, printed pp.154–155 / PDF pp.160–161, describes
continuous cochains with discrete Galois modules; section 4, printed
pp.155–156 / PDF pp.161–162, describes the field/coefficient maps and
relative-to-absolute passage. Chapter XI, section 1, printed p.165 /
PDF p.171, gives the compatible group and coefficient maps behind
inflation.

`closureRestriction` specializes pinned Mathlib's proved normal
restriction continuity from `FieldTheory/Galois/Profinite.lean`.
`closureInflationCoefficients` uses the actual module and unit-inclusion
definitions in `Cohomology`, together with the intrinsic restriction
identity from `FieldTheory/Normal/Defs.lean`.
`closureContinuousInflation` is
`ContinuousCohomology.map` from
`RepresentationTheory/Homological/ContCohomology/Functoriality.lean`.
`continuousToRelative` uses the published
`Langlands.Cohomology.Continuous.CochainComparison` construction, whose
cochain evaluation and differential certificates are reused unchanged.
The direct-limit comparison, injectivity of relative H2, and local
invariant compatibility are separate theorem obligations.
