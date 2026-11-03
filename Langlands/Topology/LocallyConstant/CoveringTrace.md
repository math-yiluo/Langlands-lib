# Finite-fiber trace of locally constant functions

This internal construction defines the unnormalized trace along an actual
covering map with finite fibers. It uses Mathlib's `IsCoveringMap`, whose
evenly covered charts allow empty fibers. Surjectivity is not assumed.

The spaces `X`, `Y`, and the optional composition target `Z` have independent
universes `u`, `v`, and `t`. The coefficient additive commutative group
`V : Type w` carries no topology. For the linear construction, `R : Type r`
is any commutative ring and `V` is an `R`-module; `r` is independent of the
other universes. There are no separation, local compactness, or ambient
compactness assumptions.

`fiberSum q f y` sums `f(x)` over the entire literal fiber
`q ⁻¹' {y}`. Its input is a family of `Finite` instances for these actual
fibers. A `Fintype` is chosen only to perform the finite sum. The sum on an
empty fiber is zero, and no division by a degree is used.
`fiberSum_eq_sum` reindexes this sum along any equivalence with a finite
type. `fiberSum_congr` identifies the sums for equal original maps.

`compFiberEquiv` identifies the fiber of `p ∘ q` over `z` with the
disjoint union of the fibers of `q` over points in the fiber of `p` over
`z`. Its forward and inverse maps use the original points and their actual
fiber equations. This proves finiteness of composite fibers and the
iterated-sum formula `fiberSum_comp`. `idFiberEquiv` identifies an identity
fiber with `Unit`; it proves `finite_id_fiber` and `fiberSum_id`.
`isCoveringMap_id` constructs the actual one-sheeted identity chart.

For group actions on `X` and `Y`, `smulFiberEquiv` uses the original action
to identify the fibers over `g⁻¹ • y` and `y` of an equivariant map.
Reindexing by it proves `fiberSum_translate`. These algebraic fiber
constructions do not require continuous actions.

`isLocallyConstant_fiberSum` uses a genuine evenly covered neighborhood of
each target point. Each inverse branch pulls the original locally constant
function back to that neighborhood. The original fiber is finite, so their
sum is locally constant; `chartFiberEquiv` identifies its value with the
literal fiber sum at every point of the chart. A neighborhood in the open
subspace then gives an open neighborhood in the target. This argument also
handles a chart with no branches.

`trace q hq` bundles that function. Its identity law is literal equality
with the original function. `trace_comp` compares the original composite
with successive traces; it explicitly assumes that `q`, `p`, and `p ∘ q`
are covering maps, together with their finite-fiber instances. The module
proves closure of finite fibers under composition, but does not prove or
assume a general closure theorem for covering maps.

`support_fiberSum_subset` proves that the nonzero locus of the sum lies in
the image of the original nonzero locus: if every summand is zero, so is
the sum. Local constancy makes the zero fiber open and hence the nonzero
locus closed. Therefore `tsupport_eq_support` identifies topological
support with that locus, and `tsupport_trace_subset` gives containment in
the image of the original topological support. A covering map is continuous.
The image of a compact support is compact, and the trace support is a
closed subset of that image. This proves `hasCompactSupport_trace` without
properness or Hausdorffness.

`traceLinearMap` proves additivity and scalar compatibility by distributing
finite sums. `trace_map` proves that every original linear coefficient map
commutes with trace, by commuting that map with the sum.

The provenance is internal: these are explicit finite sums, fiber
equivalences, and consequences of Mathlib's covering charts, locally
constant functions, and compact-support API. No result from Harris or
Berkovich is asserted here. Equivariant compact-function trace is
constructed in the companion representation module. Higher sheaf or etale
trace and the Harris realization remain separate obligations.
