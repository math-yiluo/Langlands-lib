# Archimedean completions under an isomorphism of number fields

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.InfiniteAlgEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `e : K ≃ₐ[ℚ] M` be an isomorphism of number fields. Each infinite place `W` of `M` corresponds to an infinite place `w` of `K` (through `infinitePlaceEquivOfRingEquiv`). The file shows that the completion maps between `K_w` and `M_W` are mutually inverse, and that the library's isomorphism of adele rings `adeleCongr e` acts on archimedean coordinates by these maps. This is the archimedean input for the topology of `adeleCongr`.

## Main definitions and results

- `infinitePlaceCompletionCongrHom e W`: the ring map from the completion of `K` at `w` to the completion of `M` at `W`, defined as the completion map of the place `W` lying over `w`; `infinitePlaceCompletionCongrHom_continuous` says it is continuous.
- `infinitePlaceCompletionCongrEquiv e W`: a ring isomorphism between the two completions, built from the completion maps in both directions.
- `infinitePlaceCompletionCongrHom_algebraMap`: on the image of `x ∈ K`, the completion map gives the image of `e x`.
- `adeleCongr_infiniteComponent`: for an adele `a` of `K`, the `W`-component of `adeleCongr e a` is `infinitePlaceCompletionCongrHom e W` applied to the `w`-component of `a`.

## Proofs

The two composites of completion maps are the identity because they are continuous and agree with `e ∘ e⁻¹` and `e⁻¹ ∘ e` on the dense image of the field. For `adeleCongr_infiniteComponent`, an adele of `K` is written as the image of an element of `𝔸_ℚ ⊗[ℚ] K` under `relativeAdeleBaseChangeRingEquiv`; the compatibility of `adeleCongr` with the relative version `relativeAdeleCongr` reduces the claim to pure tensors, where it follows from the transitivity of completion maps in the tower `ℚ ⊆ K ⊆ M`.

## Points to watch

- The fields carry explicit `[Algebra ℚ K]` and `[Algebra ℚ M]` instances, and `e` must be a `ℚ`-algebra isomorphism.
- `infinitePlaceCompletionCongrEquiv` is stated as a ring isomorphism only; continuity is proved for the forward map `infinitePlaceCompletionCongrHom`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/InfiniteAlgEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `6a681fc122aeb463e6618ee8a87edd5a0962076e97875da9700400abe12c7697`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
