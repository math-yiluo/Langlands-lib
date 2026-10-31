# Ordered affine covers of an open subscheme and their Čech complex of functions

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf`, in namespace
`AlgebraicGeometry`. All objects live in a fixed universe `u`.

## Definitions

**Ordered affine covers of an open.** For an open `W` of a scheme `V`, a
`Scheme.OrderedAffineCoverOf W` is a finite, linearly ordered index type `ι` with affine opens `U i`,
each contained in `W`, whose union is `W`. As for covers of the whole scheme
(`Scheme.OrderedAffineCover`), for such a cover `K`:

- `K.Idx i` is the type of strictly increasing index tuples `Fin (i + 1) → ι` (finite, with
  decidable equality);
- `K.inter s` is the intersection of the opens indexed by `s`, and `K.face s j` deletes the `j`-th
  entry of `s`.

Related constructions on covers of the whole scheme:

- `K.toCoverOf` views an ordered affine cover of `V` as a cover of the open `⊤`;
- `K.restrict π hW`, for a separated morphism `π : V ⟶ Spec R` and an affine open `W`, is the cover of
  `W` by the opens `U i ⊓ W`. These are affine because `π` is separated
  (`isAffineOpen_inf_of_isSeparated`).

**Čech complex of functions.** Let `π : V ⟶ Spec R` and `K` an ordered affine cover of `W`.

- `moduleSections π O` is the `R`-module structure on `Γ(V, O)` given by `π`.
- `K.cochain i` is the product of `Γ(V, K.inter s)` over `s : K.Idx i`.
- `res π h` is the restriction `Γ(V, O') → Γ(V, O)` as an `R`-linear map (the restriction of the
  structure presheaf `OModulePresheaf.unit π`).
- `K.d π i` is the Čech differential `(d f)(s) = ∑_{j=0}^{i+1} (-1)^j · res (f (K.face s j))`.
- `K.aug π : Γ(V, W) → K.cochain 0` is the augmentation, restricting a function on `W` to each
  `U i`.
- `K.H0 π` is the kernel of `K.d π 0`, and `K.HSucc π i` is the kernel of `K.d π (i + 1)` modulo the
  image of `K.d π i`.

The lemmas `inter_le_inter_face`, `inter_le`, `inter_le_base`, `toCoverOf_U`, `restrict_U`,
`res_apply`, `d_apply` and `aug_apply` unfold these definitions. `Scheme.OrderedAffineCover.d_toCoverOf`
says that for a cover `K` of `V` the differential of `K.toCoverOf` is the Čech differential of the
structure presheaf for `K` (by `rfl`).

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_OrderedAffineCoverOf.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_OModulePresheafHom` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
