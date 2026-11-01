# Arithmetic transport of archimedean smooth functions

Author: Worker 2.

This internal construction uses an actual number-field ring isomorphism
`e : K ≃+* L`, with independent field universes, and every natural matrix rank,
including zero. It reuses the published arithmetic map on the completion-based
infinite adele ring and the existing mixed real/complex manifold coordinates.

`mixedEquiv` conjugates the arithmetic infinite-adele ring equivalence by the
existing coordinate ring equivalences. Its two continuities follow by composition.
Its underlying additive equivalence is therefore continuously real linear,
by Mathlib's theorem that continuous additive maps between real topological
vector spaces are real linear. `matrixRealLinearEquiv` applies this map entrywise
to the actual real matrix model, with both continuities proved coordinatewise.

The induced map on matrix units is real smooth: composing with the target
units inclusion gives the continuous real-linear matrix map after the smooth
source units inclusion. The target units inclusion is an open embedding, so
Mathlib's units manifold theorem reflects smoothness through it.
`coordinates_arithmetic_map` identifies this mixed-coordinate map entrywise
with the actual completion-based arithmetic matrix map. This proves real
smoothness of that arithmetic map in the existing charts, also when applied
to the inverse field isomorphism.

`smoothComap` precomposes existing `ArchimedeanGL.SmoothFunctions L n` by this
actual arithmetic matrix map. Smooth composition proves membership of the result
in `ArchimedeanGL.SmoothFunctions K n`. The operation fixes complex values and
is complex linear. The evaluation formula, identity, contravariant composition
and two inverse identities are proved. `smoothEquiv` bundles the resulting
complex-linear equivalence, with inverse pullback along `e.symm`. Right
translation is intertwined through the actual arithmetic matrix map.

Provenance is internal composition of the published `ArchimedeanGL` and
`AdelicFunctoriality.Infinite` constructions with the pinned Mathlib continuous
additive-map theorem and units manifold construction. No new original-literature
identification is introduced. This file assigns no topology to the smooth-function
carrier and asserts no continuity for a derivative topology. It does not assert
preservation of enveloping-center finiteness, growth, cuspidality or automorphic
representation occurrence.
