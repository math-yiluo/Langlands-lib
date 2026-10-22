# Common compact-open bi-invariance: proof

`Langlands.Hecke.TestFunction.commonCompactOpenBiInvariance.{u}` proves exactly
`Langlands.Hecke.TestFunction.CommonCompactOpenBiInvarianceStatement.{u}`,
imported from `Langlands.Representation.Hecke.CommonInvarianceStatement`.
The complete theorem type is this proposition, with no additional outer
parameters or assumptions. For an arbitrary-universe Hausdorff locally compact
totally disconnected topological group, every finite set of actual
`Langlands.HarmonicAnalysis.SchwartzBruhat G` functions is bi-invariant under
one compact open subgroup contained in any prescribed open subgroup `U`.
The finite family may be empty.

The proof is an internal derivation from local constancy, compact support,
Mathlib's clopen neighborhood basis for locally compact Hausdorff totally
disconnected spaces, and elementary topological group facts. Its provenance is
the fixed Library proposition and those imported APIs. The statement's Markdown
records the original Flath motivation; this proof does not claim that the
finite-family formulation or the implemented argument is a quoted Flath theorem.
All auxiliary definitions and lemmas in this module are private.

## Open stabilizers from actual functions

`leftStabilizer f` is the subgroup of elements `g` satisfying
`f (g * x) = f x` for every `x`. Multiplication and inverse closure follow
directly from this equation. No stabilizer or invariance is supplied as input.

`left_invariant_near_one` proves that this subgroup contains a neighborhood of
`1`. At each point `(1, x)`, both maps `(g, y) ↦ f (g * y)` and
`(g, y) ↦ f y` are locally constant and have the same value. The existing
`isCompact_support f` and Mathlib's
`IsCompact.eventually_forall_of_forall_eventually` make their equality uniform
for `x` in the support. Continuity of inversion supplies the same condition
for `g⁻¹`. Intersecting these two neighborhoods extends the equality to all
points: points in the support use the first condition; if `g * x` is in the
support, the inverse condition applies at `g * x`; if neither is in the support,
both function values vanish. Thus `leftOpenStabilizer f` is an open subgroup,
using `Subgroup.isOpen_of_mem_nhds`.

`biOpenStabilizer f` intersects the left open stabilizers of `f` and of the
existing actual function `inversion f`, whose value at `x` is `f (x⁻¹)`.
`mem_biOpenStabilizer` proves left invariance directly and right invariance by
applying the latter stabilizer condition for `g⁻¹` at `x⁻¹`. This gives
`f (x * g) = f x`. It proves membership in the existing `biInvariant`
submodule. In particular the API convention `leftTranslate g f x =
f (g⁻¹ * x)` is respected because the subgroup is inverse-closed; the right
translation convention is `rightTranslate g f x = f (x * g)`.

## Compact-open refinement without an additional group hypothesis

`exists_compactOpen_inside` takes a compact neighborhood `C` of `1` and uses
Mathlib's `loc_compact_Haus_tot_disc_of_zero_dim` to choose a clopen set `V`
with `1 ∈ V ⊆ U ∩ C`. It is compact as a closed subset of `C`. Form the
existing actual test function `characteristic` of `V`, and take its left open
stabilizer `K`. Evaluating invariance at `1` shows that every `g ∈ K` has
characteristic value `1`, so `g ∈ V`. An open subgroup is closed, hence `K`
is compact as a closed subset of compact `V`, and `K ≤ U`.

This derives the required compact-open subgroup from exactly the stated
Hausdorff, local compactness, total disconnectedness, and topological group
assumptions. It does not use or assume `NonarchimedeanGroup`, a compact-open
subgroup basis, countability, unimodularity, or any Haar measure.

## Finite-family proof

The final theorem uses finite-set induction. The empty case invokes the
compact-open refinement just established. At an insertion step, intersect the
compact open subgroup already obtained with `biOpenStabilizer f` for the new
function. This intersection is open and is compact as a closed subset of the
previous compact subgroup. It remains contained in `U`. The existing
`biInvariant_antitone` transports both the new function's invariance and the
induction hypothesis to the smaller subgroup.

Worker 108 authored the proof and this explanation.
