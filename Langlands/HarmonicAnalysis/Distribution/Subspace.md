# Subspace maps for test functions and distributions

This module constructs complex linear maps on the published
`Langlands.HarmonicAnalysis.SchwartzBruhat` spaces and their full algebraic
duals `Langlands.HarmonicAnalysis.Distribution`. The ambient space `X` lies
in an arbitrary universe and carries a topology. Every subset has its
induced topology.

`SchwartzBruhat.restrictClosed hZ` restricts a test function to a closed
subset `Z`. Its value at `z : Z` is `f z.val`. Local constancy follows by
composition with the continuous inclusion, and compact support follows
by pullback along the closed embedding. This construction needs no
separation axiom on `X`.

For Hausdorff `X` and an open subset `U`,
`SchwartzBruhat.extendZero hU` extends a test function on `U` by zero.
It takes the original value at each point of `U` and is zero outside
`U`. The subset need not be closed or compact. The implementation uses
`Function.extend` along the injective subtype inclusion. Compact support
in `U` has compact image in Hausdorff `X`, so that image is closed.
Mathlib's compact-support zero-extension continuity theorem uses this
fact to control the boundary. Applying that theorem with a temporary
discrete topology on the complex codomain proves local constancy; the
definition of compact support does not depend on the codomain topology.
The discrete topology is local to this proof and supplies no new topology
on a test-function or distribution space.

The evaluation lemmas are `restrictClosed_apply`,
`extendZero_apply_subtype`, `extendZero_apply_of_mem` and
`extendZero_apply_of_not_mem`, all in the `SchwartzBruhat` namespace.
Pointwise evaluation proves linearity and `extendZero_injective`.
`support_extendZero_subset` places its nonzero support in `U`.
`tsupport_extendZero` identifies its topological support with the compact
image of the topological support in `U`; `tsupport_extendZero_subset`
places that support in `U` as well.

For any subset `Z`, without any separation or closedness hypothesis,
`Distribution.supportedOn Z` is the complex submodule consisting of
functionals `D` for which `D f = 0` whenever `f` vanishes at every point
of `Z`. The explicit membership equivalence is
`Distribution.mem_supportedOn_iff`. Closure under linear combinations
follows by evaluation. `Distribution.supportedOn_mono` says that
`Z ⊆ W` implies `supportedOn Z ≤ supportedOn W`, since vanishing on
`W` implies vanishing on `Z`. This is exactly the pointwise support
convention of the published localization and finite-orbit statements.
Those files are unchanged.

`Distribution.closedPushforward hZ` is precomposition with
`SchwartzBruhat.restrictClosed hZ`. Its evaluation formula is
`closedPushforward_apply`. A function vanishing on `Z` restricts to zero,
so `closedPushforward_mem_supportedOn` places the pushforward in
`supportedOn Z`. `closedPushforwardSupported hZ` packages this restricted
codomain explicitly, with coercion law `coe_closedPushforwardSupported`.
`Distribution.restrictOpen hU` is precomposition with
`SchwartzBruhat.extendZero hU`, and `restrictOpen_apply` is its evaluation
formula. Both are actual complex linear maps, implemented using
`LinearMap.dualMap`. Closed pushforward needs only a topology and closed
`Z`; open restriction uses Hausdorff `X` and open `U`.

## Internal provenance and scope

Worker 557 authored this internal construction from the published
`HarmonicAnalysis.Basic`, `Distribution.Basic` and
`Hecke.TestFunction` definitions, Mathlib's elementary induced-topology
and compact-support lemmas, and precomposition of linear maps.
It is a derived construction, not a transcription or proof of a theorem
from the motivating distribution-descent literature. The existing
homeomorphism transport in `Distribution.Basic` remains the transport
construction for homeomorphisms.

All maps therefore specialize to every Hausdorff locally compact totally
disconnected space, with no second-countability or sigma-compactness
assumption. No topology or continuity condition is imposed on distributions.
This module does not assert surjectivity of closed restriction,
injectivity or surjectivity of closed pushforward, descent of every
supported distribution, or a distribution equivalence. These remain
subsequent obligations. It also proves no orbit vanishing, twisted descent,
localization or Whittaker invariance theorem.
