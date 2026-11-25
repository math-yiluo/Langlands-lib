# The dimension formula for a flat morphism of locally Noetherian schemes

Module `StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.LocalRing`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

One result on local rings of schemes.

- `AlgebraicGeometry.ringKrullDim_stalk_eq_add_ringKrullDim_stalk_fiber_of_flat` (Tag 00ON, named in its docstring): for a flat morphism `φ : A ⟶ B` of locally Noetherian schemes and a point `a` of `A`, the Krull dimension of `𝒪_{A,a}` is that of `𝒪_{B,φ a}` plus that of the local ring of the fibre of `φ` over `φ a` at the point `φ.asFiber a`.

The map of local rings is flat and local, so the dimension formula for a flat local homomorphism of Noetherian local rings applies; `quotientStalkEquivFiberStalk` identifies its closed fibre with the local ring of the fibre. Dimensions take values in `WithBot ℕ∞`.

## Watch for

- The module docstring announces the comparison of local rings of fibres under base change (Tag 02FY, parts (2) and (3)), with the choice of a point at which nothing changes. The file holds none of this; its section on base change is empty.

## References

Tag 00ON. The table below lists places in EGA of which the result is a special case.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 13.2.4 | `ringKrullDim_stalk_eq_add_ringKrullDim_stalk_fiber_of_flat` | special case |
| EGA | IV 14.2.1 | `ringKrullDim_stalk_eq_add_ringKrullDim_stalk_fiber_of_flat` | special case |
| EGA | IV 21.10.7 | `ringKrullDim_stalk_eq_add_ringKrullDim_stalk_fiber_of_flat` | special case |
| EGA | IV 5.5.2 | `ringKrullDim_stalk_eq_add_ringKrullDim_stalk_fiber_of_flat` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/FibreDimensionBaseChange/LocalRing.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 16 declarations of the source file 1 are kept. The 15 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 4 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
