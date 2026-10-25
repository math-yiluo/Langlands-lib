# Finite tensor decomposition of row Schwartz–Bruhat functions

`Langlands.HarmonicAnalysis.RowTensorDecompositionStatement X d` is the
proposition that every `f : SchwartzBruhat (Fin d → X)` has a pointwise
decomposition

```text
f x = ∑ j : Fin N, c j * ∏ i : Fin d, g j i (x i),
```

for some natural number `N`, complex coefficients `c : Fin N → ℂ`, and
one-coordinate test functions `g : Fin N → Fin d → SchwartzBruhat X`.
The witnesses may depend on `f`; the equality must hold for every row `x`.
Both test-function spaces are the actual submodule carriers defined in
`Langlands.HarmonicAnalysis.Basic`: locally constant complex functions with
compact topological support. No replacement predicate or abstract tensor
product is introduced.

The complete parameter order is `X : Type u`, its `TopologicalSpace`,
`LocallyCompactSpace`, `T2Space`, and `TotallyDisconnectedSpace` instances,
then `d : ℕ`. The universe `u` is arbitrary. No algebraic structure, measure,
nonemptiness of `X`, or positivity of `d` is assumed. For `d = 0`, the row
space has one point and the empty product is `1`; the explicit coefficient
allows any value of `f` at that point, even when `X` is empty. The finite sum
may also be empty (`N = 0`).

This is an internal derived prerequisite for the row Fourier argument, authored
by Worker 128 from the task specification supplied by Worker 110. It is not a
transcription of an external theorem. Its intended use is to reduce statements
about row test functions to one-coordinate products by linearity and finite
product integration.

The proposed proof route uses the compact-open basis of a locally compact
Hausdorff totally disconnected space. Finite products of its compact-open sets
give compact-open boxes in the row space. Local constancy makes the nonzero
support clopen, hence equal to the compact topological support. Cover that
support by finitely many compact-open boxes on each of which `f` is constant.
Assign each point to the first covering box and expand the resulting
differences by inclusion-exclusion. Intersections of boxes are boxes, and a
box indicator is the product of the compact-open indicators of its coordinate
sets. The resulting finite expansion has the displayed form with complex
coefficients. Empty support and dimension zero are included by the empty-sum
and empty-product conventions.

This module only defines the proposition. The compact-open decomposition
argument remains a proof obligation; no decomposition theorem, Fourier
preservation result, or integration theorem is proved here.
