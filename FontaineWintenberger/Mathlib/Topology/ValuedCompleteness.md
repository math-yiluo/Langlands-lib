# Completeness of a valued field from its valuation ring

Module `FontaineWintenberger.Mathlib.Topology.ValuedCompleteness`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a field `F` with a `Valued F Γ₀` structure (`Γ₀` a linearly ordered commutative group with zero), the file shows that completeness of `F` for the valuation uniformity is equivalent to completeness of its valuation ring with the induced uniformity.

- `Valued.completeSpace_of_completeSpace_valuationSubring`: if the valuation subring `hv.v.valuationSubring` is complete for the uniformity inherited from `F`, then `F` is complete.
- `Valued.completeSpace_iff_completeSpace_valuationSubring`: `F` is complete if and only if its valuation subring is complete.

For the first statement, the valuation ring is an open neighbourhood of `0`, so a Cauchy filter on `F` eventually lies in a translate `a + 𝒪` of the valuation ring; translation is a uniform embedding, so the translate is complete and the filter converges. The converse direction uses that the valuation ring is closed in `F`.

## What to watch for

- The value group `Γ₀` is arbitrary: no rank-one or discreteness assumption.
- Both statements are theorems, not instances; they lie in Mathlib's `Valued` namespace.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib/Topology/ValuedCompleteness.lean` (SHA-256 of the source file `389fa8cd68060c977526806f512e6f469833b85cdc2d05ea1607a9f68294f6cf`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
