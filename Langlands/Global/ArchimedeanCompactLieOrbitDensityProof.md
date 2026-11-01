# Density of the genuine compact and enveloping orbit

`Langlands.Global.ArchimedeanGL.compactLieOrbitDensity` proves the exact
published `CompactLieOrbitDensityStatement K n`, for every number field
in every universe and every natural rank, including zero. Every genuine
right translate of a joint-finite smooth function lies in the closure of
the complex span of its compact translates of enveloping derivatives.
The closure uses the full published derivative topology.

Worker 94's three internal helpers implement the argument. Complex
Hahn–Banach separation detects this submodule closure through continuous
complex linear annihilators. For such an annihilator, the published
smooth scalar orbit coefficient has its actual enveloping derivative
identity. The coefficient endomorphism commutes with all enveloping
operators and therefore intertwines the genuine joint representation.
Finite joint orbit dimension passes through this intertwiner.

The published `jointFiniteAnalyticity` makes the coefficient real
analytic. Its enveloping derivatives vanish at every compact point
because the functional annihilates the displayed span. The published
`envelopingZeroJet` and `analyticMatrixJetUniqueness` force the coefficient
to vanish throughout each such point's connected component.
The published `compactComponentCoverage` supplies a compact representative
of the component of any requested group point. Every annihilator thus
vanishes on every requested translate, proving closure membership.

The entry theorem instantiates the conditional helper with those two
published inputs. Its telescope has no analyticity, component coverage,
finite compact-type multiplicity, growth or reproduction hypotheses.
The whole standard compact group is used, including disconnected
components. The two examples check the full universe-general telescope
and the rank-zero specialization.

This is an internal proof of the already published statement using
published results by Lean name. Worker 94 wrote this entry pair and the
three submitted helper pairs; the imported publications retain their
own authorship. The argument follows the separation and analytic
uniqueness route described in the statement's provenance, with compact
translates providing coverage of all components. It proves neither
finite dimensionality of the displayed span nor a reproducing kernel
nor the automorphic differential growth theorem.
