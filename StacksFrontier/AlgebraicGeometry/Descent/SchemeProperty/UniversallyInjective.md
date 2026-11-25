# Generalizing maps preserve generic points

Module `StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.UniversallyInjective`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

One lemma of topology.

- `AlgebraicGeometry.genericPoints_map_of_generalizingMap`: let `g : X → Y` be a generalizing map between quasi-sober `T₀` spaces. If `x` is a generic point of an irreducible component of `X` (Mathlib's `genericPoints X`), then `g x` is one of `Y`.

A point is in `genericPoints` when every point specializing to it equals it (`mem_genericPoints_iff_forall_specializes_eq`); a generalization of `g x` lifts, `g` being generalizing, to a generalization of `x`, which is `x` itself.

## Watch for

- The module docstring announces a criterion for a flat separated morphism to be universally injective (Tag 09NP), in terms of the generic points of its source. The file does not hold it; the lemma above is one of its steps.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Descent/SchemeProperty/UniversallyInjective.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 2 declarations of the source file 1 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.universallyInjective_of_flat_of_separated_of_genericPoints_injOn`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
