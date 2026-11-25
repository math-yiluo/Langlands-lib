# Flat quotients in directed systems

Module `StacksFrontier.RingTheory.SpreadingOut.QuotientSystem`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Quotienting a directed system by the inverse images of a proper ideal of its colimit gives a new system to which flatness descent applies.

In `Stacks.SpreadingOut.QuotientSystem`, `idealA` is the inverse image Iᵢ of I in Aᵢ, and `idealB` is its extension IᵢBᵢ. The functors `funA`, `funB` and `funN` take the corresponding quotients of the stage rings Aᵢ, Bᵢ and modules Nᵢ. For a nonempty directed system with compatible colimit maps to R, S and M, `legAIsColimit`, `legBIsColimit` and `legNIsColimit` give colimits R/I, S/IS and M/IM.

`Module.Flat.exists_ge_flat_quotient_of_isColimit` assumes local stage rings with local structure maps Aᵢ → Bᵢ, each Aᵢ essentially of finite type over ℤ and each Bᵢ essentially of finite type over Aᵢ. The Nᵢ are finite over Bᵢ. Each Bⱼ is a prime localization of the base change of Bᵢ to Aⱼ, and the module transitions are base changes. If M/IM is flat over R/I, then above any given index there is a stage with Nⱼ/IⱼNⱼ flat over Aⱼ/Iⱼ.

The quotient colimit proofs lift representatives and finite sums witnessing membership in IS or IM to stages. The flatness proof checks that the quotients preserve the localization and base-change properties of the transitions, as well as locality and finiteness, then applies `Module.Flat.exists_ge_flat_of_isColimit` to the quotient system.

The theorem assumes locality of the Aᵢ → Aⱼ transitions explicitly as `hAmaplocal`, and all types share a universe. The construction forms the module quotient using (IᵢBᵢ)Nᵢ to obtain a Bᵢ/IᵢBᵢ-action. With compatible scalar actions, `Stacks.SpreadingOut.QuotientSystem.quotSMulTopEquiv` identifies this with the quotient formed over Aᵢ as an Aᵢ/Iᵢ-module.

The system follows Tag 00QX, and the flatness argument applies Tag 00R6.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/SpreadingOut/QuotientSystem.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 61 declarations of the source file 56 are kept. The 5 left out are not needed by the results for which the extract is made: `Stacks.SpreadingOut.QuotientSystem.funA_map_mk`, `Stacks.SpreadingOut.QuotientSystem.funPhi_app_mk`, `Stacks.SpreadingOut.QuotientSystem.legA_app_mk`, `Stacks.SpreadingOut.QuotientSystem.legB_app_mk`, `Stacks.SpreadingOut.QuotientSystem.legN_app_mk`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
