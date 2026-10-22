# Proof of compact-open fixed-vector duality

This module proves the entire
`SmoothDualCompactFixedDualityStatement`, with all helpers in the same file.

Three internal finite-orbit facts support the argument. A linear map constant
on an orbit has that same value on its normalized mean; the orbit is nonempty,
so its cardinality is nonzero in the complex numbers. Left translation
permutes the orbit and hence fixes its mean. Replacing the starting vector by
a translate leaves the orbit itself unchanged and hence leaves the mean
unchanged.

For a smooth representation and a compact open subgroup, the accepted
`finite_orbit_of_smooth` supplies finite orbits. The accepted `averageMap` is
therefore restricted to a linear map `P` into the fixed vectors. The first
finite-mean fact shows `P` fixes each fixed vector, and the orbit equality
shows `P(rho(k)v) = P(v)` for `k` in the subgroup.

A fixed smooth functional has constant values on each subgroup orbit: evaluate
its dual fixedness equation at the inverse group element. Its value on `P(v)`
is therefore its value on `v`. Consequently two such functionals with the same
restriction agree everywhere. Conversely, composing any functional on the
fixed vectors with `P` produces a functional fixed by the open subgroup. That
subgroup witnesses smoothness, so the extension belongs to the smooth dual.
Since `P` fixes fixed vectors, its restriction is the original functional.

The closing theorem introduces the topological-group instance only at the
target's internal binder and proves its complete quantified proposition.
There is no assumption of projection, exactness, admissibility or reflexivity.
The separate compact-averaging task remains responsible for its own public
projection/naturality and surjectivity interfaces.

The route follows Casselman II.3.1, page 6, using the normalized finite sum
behind II.1.2, pages 3-4, directly instead of a separately bundled direct-sum
decomposition. The complex-coefficient specialization is documented in
`CompactDualityStatement.md`. The original source is Bill Casselman,
*Introduction to admissible representations of p-adic groups*, Chapter II:
*Smooth representations*, revision June 16, 2019, Section 3, Proposition II.3.1,
page 6, and Section 1, Proposition II.1.2, pages 3-4. The stronger ambient
conventions appear on page 1. The literature ID is
`casselman-2019-smooth-representations`, content SHA256
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
The retained original is
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

## Published interfaces and validation status

The target is the published declaration
`Langlands.SmoothDualCompactFixedDualityStatement` in
`Langlands.Representation.Smooth.Contragredient.CompactDualityStatement`.
The proof imports `Langlands.Representation.Compact.Definitions`, using
`Compact.finite_orbit_of_smooth`, `Compact.averageMap`, `Compact.orbitMean`
and its finite-sum description. These averaging constructions are by Worker 5.
The target imports `Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions`,
which supplies `smoothDualFixedRestriction`. Its dependencies provide smoothness,
the smooth part, the algebraic and smooth contragredients, and fixed vectors.
All 18 project source files in this import closure match the current Library
at `843c574c920aa9926ab56adf662c74b3cd4ed0e1`.

The closing theorem now explicitly declares its outer parameters in the
published statement's order: group carrier, group structure, topology, module
carrier, additive structure, and complex scalar action. The previous inferred
order put the topology after the module parameters. Pointwise uses of the old
theorem still proved the quantified mathematical proposition, but the unapplied
theorem constant failed the complete declaration-type check. This correction
changes only the closing declaration's parameter order; all finite-mean helpers,
the restriction-bijectivity argument, and the theorem body are unchanged.
The topological-group and smoothness hypotheses remain internal to the target.

Worker 0 authored the proof and original explanation. Worker 48 verified the
source correspondence and dependencies, compiled the original proof, and
expanded its documentation. Worker 0 diagnosed the outer-binder mismatch and
prepared this correction. The corrected contribution explicitly replaces the
rejected original submission, whose history is preserved. It still requires
formal machine validation, independent semantic review and publication.
No retired independent replay or
module-wide audit is requested. The pinned environment uses Lean 4.34.0 and
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

Worker 0 then compiled the corrected proof with the pinned Lean executable,
using freshly built project dependencies whose sources match the current
Library. The proof returned exit 0 without diagnostics. A second command
assigned the unapplied constant `@Langlands.smoothDualCompactFixedDuality`
directly to the statement's complete outer telescope, with independent group
and module universes; it returned exit 0. The same direct check failed on the
original candidate precisely because of the topology parameter's position.
These are development checks, not independent acceptance or publication.

Worker 48 verified the correction with incremental Lake check
`3083a8c8-1dff-4266-8b9b-f8df28562d7e`: the corrected proof compiled without
warnings or errors. Inspection retained independent universe parameters `uG`
and `uV`, with only `propext`, `Classical.choice`, and `Quot.sound`.
A second successful Lake check,
`eb0db841-135c-44e6-b1e1-ed06f57f8adc`, compiled a direct assignment of
`@Langlands.smoothDualCompactFixedDuality` to the complete statement telescope.
It also reported zero warnings and errors. This checks the corrected binder
order without first applying or rearranging the theorem's parameters.
