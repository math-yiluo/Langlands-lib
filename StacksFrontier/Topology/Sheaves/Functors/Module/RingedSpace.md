# The pullback–pushforward adjunction for module sheaves

Module `StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A morphism f : X ⟶ Y of ringed spaces gives an adjoint pair on sheaves of modules over the structure sheaves. Pushforward evaluates a sheaf on inverse images of opens and restricts scalars along the structure map of f.

## Construction

`structureSheafRing` views the commutative structure sheaf as a sheaf of rings, and the functors act on Mathlib's `SheafOfModules` over it. In `RingedSpaceModuleAdjunction`, `structureSheafHom` is the structure map `O_Y ⟶ f_* O_X`, using the continuous functor `opensMap` of inverse images of opens.

- `modulePushforward` is the module pushforward along this map. The instance `pushforward_structureSheafHom_isRightAdjoint` obtains a left adjoint from the corresponding presheaf construction and Mathlib's site-level adjointness result; `modulePushforward_isRightAdjoint` restates it for `modulePushforward`.
- `modulePullback` uses Mathlib's chosen left adjoint. Its usual description is inverse image followed by extension of scalars to the source structure sheaf. `modulePullbackPushforwardAdjunction` gives the adjunction.

The spaces, rings and modules share one universe. The lemma `coversTop_preimage` takes an open cover of the target, indexed by I, to the cover of the source by the preimages, indexed by `ULift I`. The module docstring also lists a name for the category of module sheaves, the hom bijection of the adjunction, the pullbacks of the structure sheaf and of free module sheaves, and the additivity of both functors; these are not in the file.

Pushforward is part (1) of Tag 0095. The adjoint pair is Tag 0096. Related references include EGA 0 4.2.1, EGA 0 4.3.1 and EGA 0 4.4.3, and SGA 4 IV 13.2 and SGA 4 IV 13.4.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0095](https://stacks.math.columbia.edu/tag/0095) | `modulePushforward` | (1) |
| [0096](https://stacks.math.columbia.edu/tag/0096) | `modulePushforward` |  |
| [0096](https://stacks.math.columbia.edu/tag/0096) | `modulePullback` |  |
| [0096](https://stacks.math.columbia.edu/tag/0096) | `modulePullbackPushforwardAdjunction` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 4 III 1.9.1 | `opensMap` | special case |
| SGA | 4 III 1.9.1 | `opensMap_isContinuous` | continuity of f^{-1} |
| SGA | 4 IV 4.1.1 | `opensMap_isContinuous` | partial |
| EGA | 0 4.2.1 | `modulePushforward` | Ψ_* functor |
| SGA | 4 Vbis 1.3.6 | `modulePushforward` | ringed spaces, φ_* |
| EGA | 0 12.2.1 | `modulePushforward` |  |
| SGA | 3 VIIA 1.1 | `modulePushforward` | more general |
| SGA | 4 IV 13.2.1 | `modulePushforward` | special case |
| SGA | 4 V 5.0 | `modulePushforward` | special case |
| EGA | 0 4.4.3 | `pushforward_structureSheafHom_isRightAdjoint` | partial |
| SGA | 4 Vbis 1.3.6 | `pushforward_structureSheafHom_isRightAdjoint` | partial |
| SGA | 6 VI 2.3.1 | `pushforward_structureSheafHom_isRightAdjoint` | partial |
| EGA | 0 4.2.1 | `modulePushforward_isRightAdjoint` | more general |
| SGA | 4 Vbis 1.3.6 | `modulePushforward_isRightAdjoint` | partial |
| SGA | 6 VI 2.3.1 | `modulePushforward_isRightAdjoint` | partial |
| SGA | 4 IV 13.2.2 | `modulePullback` | ringed space, comm O |
| SGA | 4 IV 13.2 | `modulePullback` | u^* for ringed spaces |
| SGA | 4 Vbis 1.3.6 | `modulePullback` | ringed spaces, φ^* |
| SGA | 4 XVII 4.1 | `modulePullback` | ringed spaces |
| EGA | 0 4.3.1 | `modulePullback` |  |
| SGA | 3 III 0.1.4 | `modulePullback` | more general |
| SGA | 6 IV 2.6 | `modulePullback` | special case |
| SGA | 6 VI 2.3.1 | `modulePullback` | more general |
| SGA | 4 IV 13.4 | `modulePullbackPushforwardAdjunction` | a), ringed spaces |
| SGA | 4 Vbis 1.3.6 | `modulePullbackPushforwardAdjunction` | ringed spaces |
| EGA | 0 4.4.3 | `modulePullbackPushforwardAdjunction` | partial |
| EGA | III 7.7.9 | `modulePullbackPushforwardAdjunction` | more general |
| SGA | 3 I 4.6.4 | `modulePullbackPushforwardAdjunction` | more general |
| SGA | 4 IV 14.2 | `modulePullbackPushforwardAdjunction` | special case |
| SGA | 6 VI 2.3.1 | `modulePullbackPushforwardAdjunction` | more general |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Sheaves/Functors/Module/RingedSpace.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 18 declarations of the source file 10 are kept. The 8 left out are not needed by the results for which the extract is made: `RingedSpaceModuleAdjunction.ModuleSheaves`, `RingedSpaceModuleAdjunction.homEquiv`, `RingedSpaceModuleAdjunction.modulePullbackObjFreeIso`, `RingedSpaceModuleAdjunction.modulePullbackObjUnitIso`, `RingedSpaceModuleAdjunction.modulePullback_additive`, `RingedSpaceModuleAdjunction.modulePushforward_additive`, `RingedSpaceModuleAdjunction.moduleSheaves_eq`, `RingedSpaceModuleAdjunction.moduleSheaves_instCategory_eq`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 30 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
