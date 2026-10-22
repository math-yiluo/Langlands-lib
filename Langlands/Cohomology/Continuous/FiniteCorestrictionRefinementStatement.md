# Refinement compatibility for finite-stage corestriction

Statement by Worker 22. The proposition records a proof obligation for the
concrete finite-stage corestriction; it does not assert a proof. Its
finite-corestriction, ordinary-corestriction, and quotient-transport
definitions are published. This proposition is a separate statement
submission; an exact proof task follows its acceptance and publication.

`Langlands.Continuous.FiniteCorestrictionRefinement : Prop` quantifies
over an arbitrary common universe `u`, a commutative ring `k`, a compact
topological group `G`, any representation `A : Rep k G`, an open subgroup
`H`, and open normal subgroups `M ≤ N ≤ H`. For every natural degree
`q`, it asserts the equality

```
Inf_(H/(H∩N) → H/(H∩M)) ; Cor_M = Cor_N ; Inf_(G/N → G/M).
```

The arrows in this display indicate the direction of the cohomology
maps; the underlying quotient group homomorphisms go in the opposite
direction. Both inflations are precisely the existing `finiteInflation`,
with the inclusion of the actual fixed submodules. The subgroup
refinement uses `restrictOpenNormal_le H hMN`. The two corestrictions
are the composites in `finiteCorestriction`, through the actual image
subgroups of `H` in `G/M` and `G/N` and the standard-resolution ordinary
corestriction. Containment of `M` in `H` is derived from the two supplied
containments. Nothing asserts that either inflation is injective.

This is the coherence equation needed to construct the corestriction
cocone on the final ambient indexing functor `transferIndexFunctor H`.
It assumes neither a transfer compatibility law nor a continuous
comparison theorem. Compactness supplies finite quotient cardinalities;
no Hausdorff or total-disconnectedness assumption occurs. The finite
stage does not require coefficient topology. The degree-zero case is
included, as are all higher natural degrees.

The provenance is derived: Serre, *Local Fields*, Greenberg translation
(1979), Chapter VII, Section 5, printed pages 115–116 / PDF pages
121–122, fixes the compatible-map and inflation conventions; Section 7,
printed pages 118–119 / PDF pages 124–125, constructs finite-index
corestriction; Chapter X, Section 3, printed page 154 / PDF page 160,
uses the inflation-indexed limit. The particular refinement equation
for these Lean maps is an explicit proof obligation, not a quoted
result or an assumed limit construction.
Literature ID `serre-1979-local-fields`; source SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`;
retained file `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
