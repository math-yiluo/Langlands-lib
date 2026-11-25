# The ramification filtration under the field-of-norms correspondence

Module `FontaineWintenberger.FieldOfNorms.Galois.Filtration`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy `IsPerfectResidueLocalField`, `L/K` an infinite separable APF extension, and `M/L` separable. The file transports the upper ramification filtration to the Galois group of `RelFieldOfNorms K L M` over `FieldOfNorms K L`, and compares it with the filtration of `M/K`.

- `RelFieldOfNorms.normUpperRamificationGroup K L M u`: the image of `RelFieldOfNorms.upperRamificationGroup K L M u` under `RelFieldOfNorms.autEquiv`.
- `RelFieldOfNorms.normGaloisEmbedding`: the injective homomorphism from that Galois group to `M ≃ₐ[K] M`; its image is that of `M ≃ₐ[L] M`.
- `RelFieldOfNorms.map_normUpperRamificationGroup`: for `M/K` Galois and `u ≥ −1`, the image of the group at `apfPsi K L u` equals `upperRamificationGroupInfinite K M u` intersected with the image of the embedding. The file names this Wintenberger's Corollary 3.3.6; `L/K` need not be normal.
- `RelFieldOfNorms.autEquiv_mem_normUpperRamificationGroup_apfPsi_iff`: the same for one automorphism.

The proofs apply `RelFieldOfNorms.map_upperRamificationGroup` and `upperRamificationGroup_eq_comap`, from imported files.

The filtration on the norm side is defined by transport of the library's own group on `M ≃ₐ[L] M`.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, Corollary 3.3.6.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Galois/Filtration.lean` (SHA-256 of the source file `5249ffe18cbfbeb71e4ab4bc88085c58ade9cf83728b2a8663e1ef23a03595a3`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
