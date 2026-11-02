# Actual block constant terms and the original general-linear integrals

This derived comparison uses the existing general-linear group scheme over an
arbitrary number field `F`, the existing two-block subgroup functor with
`a + b = n`, and its actual principal-image rational quotient. It compares
the actual constant term with the original
`Langlands.Automorphic.constantTerm` through the already constructed
`continuousGeneralLinearEquiv`. Empty blocks remain allowed.

The reconstruction identity `blockUnipotent_adelicCoordinates` identifies the
original block matrix of the actual point coordinates with the ambient matrix
of that same actual point. Induction on the actual quotient, the original
matrix integrand's representative formula and evaluation compatibility then
prove `constantTermIntegrand_generalLinearBlock`: the actual integrand is the
original matrix integrand composed with `quotientHomeomorph`.

All measures here use the Borel sigma algebras of the already constructed
topologies. Under the explicit hypothesis `CompactSpace (AdeleQuotient F)`,
the measure is exactly `rationalQuotientMeasure`, whose forward pushforward is
the original normalized probability measure `matrixQuotientHaar`. Measure
preservation and the measurable embedding of the homeomorphism give both the
integrability equivalence and the integral identity
`constantTerm_generalLinearBlock`. The original compact matrix convergence
theorem separately proves `hasConvergentConstantTerm_generalLinearBlock`;
convergence is therefore established independently of any totalized integral
value.

`generalLinearBlockConstantTermLinearMap` is the actual normalized integral as
a complex linear map on the full continuous rational-invariant space. Its
evaluation agrees with the original matrix constant term. The existing generic
integral laws give compatibility with positive ambient right translation and
left invariance under the actual two-block subgroup, using the proved
measure-preservation law for its quotient translation.

Finally, `hasVanishingConstantTerm_generalLinearBlock_iff` identifies convergence
and vanishing at every actual ambient point with vanishing of the original
block constant term at every original adelic matrix. Surjectivity of the actual
ambient point comparison supplies the quantifier change.

The provenance is internal: the proof composes the actual point, quotient and
normalized measure comparisons with the original constant-term and ambient
function constructions. No new external structural theorem is invoked. This
unit does not prove compactness of the additive adele quotient, general
reductive finite volume or reduction theory, nor identify an independently
normalized ambient Haar quotient. It does not identify this supplied block
family with all rational parabolics or construct smooth, growth or Hilbert
realizations of cusp forms.
