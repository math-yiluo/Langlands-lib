# The standard ordered affine cover of projective space

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover`, in namespace
`AlgebraicGeometry.ProjSpace`. All objects live in a fixed universe `u`.

## Definitions

- `stdCover R n` is the ordered affine cover of `ℙⁿ_R = Proj R[X₀, …, Xₙ]` by the basic opens
  `D₊(Xⱼ)`, indexed by `Fin (n + 1)` (lifted to universe `u`). These opens are affine because `Xⱼ` has
  degree `1`, and they cover `ℙⁿ_R` because the irrelevant ideal lies in `(X₀, …, Xₙ)`
  (`irrelevant_le_span_X`).
- `stdCoverPullback ι`, for an affine morphism `ι : W ⟶ ℙⁿ_A`, is the ordered affine cover of `W` by the
  preimages `ι⁻¹(D₊(Xⱼ))`.

`stdCover_U` and `stdCoverPullback_U` unfold these definitions (by `rfl`).

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_ProjSpaceCover.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_ProjSpace` and
  `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` are renamed to
  `Langlands.AnthropicFLT.Definitions.*`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
