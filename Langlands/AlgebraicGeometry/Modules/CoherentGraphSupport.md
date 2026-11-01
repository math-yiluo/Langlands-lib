# Coherent graphs and smaller support errors

This internal prerequisite derives closed support bounds for the actual graph
constructed in `CoherentGraph`. It does not assert an Euler polynomial.

If a module vanishes outside an irreducible closed subset `T` of height at most
`d` and on an open subset `U` meeting `T`, it vanishes outside the closed subset
`T \ U`. Every irreducible closed subset of `T \ U` misses a point of `T`.
The strict inclusion raises height by at least one, so its height is less than
`d`. This proves `HasSupportDimensionLT` with bound `d`. The argument uses
the height inequality from `NoetherianVanishing.Topology` and does not require
noetherianity or quasi-coherence.

Consequently, a map that becomes an isomorphism on `U` has a kernel with that
smaller support bound when its source vanishes outside `T`, and a cokernel
with that bound when its target vanishes outside `T`.

On a separated scheme the inclusion of an affine open is affine: it factors
through the affine-open spectrum isomorphism and the affine `fromSpec` map.
Affine pushforward preserves quasi-coherence, and the pullback closure from
`CoherentGraph` proves quasi-coherence of the graph of two quasi-coherent modules.
If the scheme is locally noetherian and both modules have finite sections on
all affine opens, the graph has the same finiteness property. No finiteness
of the pushforward target is required.

The graph embeds in the binary direct sum of its two modules. It therefore
vanishes on every open on which both modules vanish. Both graph projections
become isomorphisms on `U`. If the two modules vanish outside `T` and `U`
meets `T`, the kernels and cokernels of both projections thus have support-height
bound `d`, where `T` has height at most `d`. The Prop-valued predicate
`CoherentGraph.HasSupportErrorsLT` denotes exactly the conjunction of these
four support bounds; `lowerSupportErrors` proves it under the stated hypotheses.
The four errors are also quasi-coherent and have finite affine sections under
the same separated, locally noetherian, affine-open and coherent-module
hypotheses used above, by the kernel and cokernel closure lemmas.

All constructions are the categorical kernels, cokernels, pullbacks and direct
sums in the actual scheme-module category. The provenance is internal:
the proof combines the existing graph construction, open restriction, affine
pushforward and elementary height inequalities. It assumes no Euler polynomial,
generic rank comparison or positivity statement.
