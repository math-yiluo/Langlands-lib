# Pulling back ordered affine covers along affine morphisms

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap`, in namespace
`AlgebraicGeometry.Scheme.OrderedAffineCover`. All schemes live in a fixed universe `u`.

## Definitions and results

- `preimage_iInf_fin` (theorem): for a morphism `f : Y ⟶ Z` and finitely many opens `W j` of `Z`
  indexed by `Fin (n + 1)`, `f⁻¹(⋂ⱼ W j) = ⋂ⱼ f⁻¹(W j)`.
- `𝒰.comap f`, for an ordered affine cover `𝒰` of `X` and an affine morphism `f : Y ⟶ X`, is the
  ordered affine cover of `Y` with the same index type and order and opens `f⁻¹(U i)`. These are affine
  because `f` is affine, and they cover `Y`.
- `𝒰.baseChange π A`, for `π : X ⟶ Spec R` and an `R`-algebra `A`, is the pullback of `𝒰` to the fibre
  product `X ×_{Spec R} Spec A` along the first projection, which is affine (`isAffineHom_fst`).

The lemmas `comap_ι`, `comap_U`, `comap_Idx`, `comap_face`, `baseChange_ι`, `baseChange_U`,
`baseChange_Idx` and `baseChange_face` hold by `rfl`. `comap_inter` and `baseChange_inter` say that the
intersection `inter s` of the pulled-back cover is the preimage of the intersection for `𝒰`, and
`comap_inter_le`, `le_comap_inter`, `baseChange_inter_le` and `le_baseChange_inter` are its two
inclusions. `TwoAffineOpenCover.toOrderedAffineCover_pullback` says that pulling a two-affine cover back
to `X ×_{Spec R} Spec A` and then ordering it gives the base change of its ordered cover.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_OrderedAffineCoverComap.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
