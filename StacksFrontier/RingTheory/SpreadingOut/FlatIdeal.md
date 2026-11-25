# Spreading out flatness along a proper ideal

Module `StacksFrontier.RingTheory.SpreadingOut.FlatIdeal`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A test on the tensor product of one proper ideal, together with flatness modulo that ideal at cofinally many stages, gives flat models arbitrarily far along a directed system.

`Module.Flat.exists_ge_flat_of_isColimit_of_rTensor_subtype_injective` considers stages Aᵢ → Bᵢ of local rings with local, essentially finite type structure maps. Each Aᵢ is essentially of finite type over ℤ, and Nᵢ is finite over Bᵢ. The transitions identify Bⱼ with a prime localization of the tensor product of Bᵢ and Aⱼ over Aᵢ and Nⱼ with the corresponding base change of Nᵢ. The rings Aᵢ and modules Nᵢ have colimits R and M, with compatible maps from Bᵢ to an R-algebra S acting on M. For a proper ideal I of R, write Iᵢ for its inverse image in Aᵢ. If `hTor` says that each finite relation ∑ pₖmₖ = 0 with pₖ ∈ I already gives ∑ pₖ ⊗ mₖ = 0 in I ⊗ M over R, and `hQflat` gives flatness of Nᵢ/IᵢNᵢ over Aᵢ/Iᵢ cofinally, then some Nⱼ above any prescribed index is Aⱼ-flat.

Noetherianity gives finitely many generators for the ideal and for their relations on the stage module. The tensor relations vanish in the colimit by `hTor` and hence at a common later stage. The quotient flatness criterion then applies at a stage supplied by `hQflat`.

All the types share one universe. The tensor injectivity test concerns just I, and the flatness of the stage quotients is a separate hypothesis. The colimit hypotheses concern A and N.

The file refers to Tag 00QX for the system of models and Tag 00R6 for the related flatness theorem.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/SpreadingOut/FlatIdeal.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
