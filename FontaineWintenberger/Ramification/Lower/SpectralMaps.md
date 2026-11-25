# Maps of spectral integer rings and residue fields along field embeddings

Module `FontaineWintenberger.Ramification.Lower.SpectralMaps`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete nontrivially normed ultrametric field and `E`, `L` algebraic extensions of `K`, each with its spectral valuation. A `K`-embedding `i : E →ₐ[K] L` preserves the spectral norm, so it induces maps on the rings of integers and on the residue fields.

- `spectralValuation_hasExtension_tower`: in a tower `K ⊆ E ⊆ L`, the spectral valuation of `L` extends that of `E`.
- `spectralIntegerInclusion K i`: the restriction of `i` to the spectral integer rings, as an algebra map over `𝒪[K]`.
- `spectralIntegerInclusion_isLocalHom`: this map is local.
- `spectralResidueInclusion K i`: the induced map of residue fields, an algebra map over `𝓀[K]`; it is injective.
- `spectralIntegerInclusion_comp`, `spectralResidueInclusion_comp`: both constructions respect composition of embeddings.

The tower statement rests on Mathlib's `spectralNorm.eq_of_tower`.

The extensions need only be algebraic: no finiteness of degree and no discreteness of the valuation is assumed. `spectralIntegerRing` and `spectralValuation` are the library's notions built from the spectral norm.

Reference: Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/SpectralMaps.lean` (SHA-256 of the source file `6e79b0c2aa46642ad58f236f85b746bb851005726a68d4cb825c37c5cdf430c4`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
