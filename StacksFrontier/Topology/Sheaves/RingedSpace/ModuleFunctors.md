# Composition of module pushforward and pullback

Module `StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For composable morphisms f and g of ringed spaces, pushing forward along g ∘ f agrees with successive pushforward, and pulling back along g ∘ f agrees with pullback along g followed by pullback along f.

`ringCatSheaf` forgets commutativity of the structure sheaf to define `Modules` using Mathlib's `SheafOfModules`. The structure morphism induces `pushforward`, its left adjoint `pullback`, and `pullbackPushforwardAdjunction`.

`pushforwardComp` uses the factorization of the structure morphism of a composite and Mathlib's composition isomorphism for module pushforwards. `pullbackComp` follows by uniqueness of left adjoints. Both comparisons are natural isomorphisms, including the pushforward comparison stated as an equality in the source. The constructions use one universe for the spaces, rings, and module sections.

References include Stacks Project Tag 0097, EGA 0 4.2.1, 0 4.2.6, 0 4.3.1, 0 4.3.6 and 0 4.4.3, and SGA 4 IV 13.2.1, 4 IV 13.2.2 and 4 IV 13.4.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0097](https://stacks.math.columbia.edu/tag/0097) | `pushforwardComp` | (1) |
| [0097](https://stacks.math.columbia.edu/tag/0097) | `pullbackComp` | (2) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 4.1.1 | `ringCatSheaf` |  |
| EGA | 0 4.1.3 | `Modules` | special case |
| SGA | 2 I 1.7 | `Modules` | partial |
| SGA | 4 II 6.3.2 | `Modules` | special case |
| SGA | 4 II 6.7 | `Modules` | special case |
| SGA | 4 IV 11.1.2 | `Modules` | special case |
| SGA | 4 V 3.5 | `Modules` | special case |
| SGA | 4 V 6.13 | `Modules` | special case |
| SGA | 6 I 4.8 | `Modules` | partial |
| SGA | 6 II 2.0 | `Modules` | Mod for a ringed space |
| SGA | 6 II 2.3.2 | `Modules` | Mod(S), special case |
| SGA | 6 III 5.1 | `Modules` | special case |
| EGA | 0 12.2.1 | `pushforward` |  |
| EGA | 0 4.2.1 | `pushforward` |  |
| EGA | II 1.1.1 | `pushforward` | partial |
| SGA | 3 VIIA 1.1 | `pushforward` | more general |
| SGA | 4 IV 11.2.2 | `pushforward` | special case |
| SGA | 4 IV 13.2.1 | `pushforward` | special case |
| SGA | 4 Vbis 1.3.6 | `pushforward` | special case |
| EGA | 0 4.3.1 | `pullback` |  |
| EGA | I 9.1.8 | `pullback` | more general |
| EGA | III 1.4.15 | `pullback` | partial |
| EGA | III 4.7.1 | `pullback` | more general |
| EGA | IV 2.1.4 | `pullback` | more general |
| EGA | IV 2.5.1 | `pullback` |  |
| EGA | IV 9.4.1 | `pullback` | more general |
| SGA | 3 I 4.6.1 | `pullback` | more general |
| SGA | 3 III 0.1.4 | `pullback` | more general |
| SGA | 4 IV 13.2.2 | `pullback` | special case |
| SGA | 4 Vbis 1.3.6 | `pullback` | special case |
| SGA | 4 XVII 4.1 | `pullback` | special case |
| SGA | 6 IV 2.6 | `pullback` | special case |
| SGA | 6 VI 2.3.1 | `pullback` | more general |
| EGA | 0 4.4.3 | `pullbackPushforwardAdjunction` |  |
| EGA | III 7.7.9 | `pullbackPushforwardAdjunction` | more general |
| SGA | 3 I 4.6.4 | `pullbackPushforwardAdjunction` | more general |
| SGA | 3 VIB 11.4 | `pullbackPushforwardAdjunction` | Last equality of (†) |
| SGA | 4 IV 13.4 | `pullbackPushforwardAdjunction` | special case |
| SGA | 4 IV 14.2 | `pullbackPushforwardAdjunction` | partial |
| SGA | 4 Vbis 1.3.6 | `pullbackPushforwardAdjunction` | adjunction φ* ⊣ φ_* |
| SGA | 6 VI 2.3.1 | `pullbackPushforwardAdjunction` | more general |
| EGA | 0 4.1.1 | `toRingCatSheafHom_comp` | partial |
| EGA | 0 4.2.6 | `pushforwardComp` |  |
| EGA | 0 4.3.6 | `pullbackComp` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Sheaves/RingedSpace/ModuleFunctors.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 44 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
