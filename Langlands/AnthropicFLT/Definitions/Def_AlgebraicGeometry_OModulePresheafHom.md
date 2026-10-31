# Morphisms and short exact sequences of presheaves of modules, and induced maps on Čech cohomology

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom`, in namespace
`AlgebraicGeometry`. All objects live in a fixed universe `u`. Throughout, `π : V ⟶ Spec R` for a
commutative ring `R`, and `OModulePresheaf π` is the notion of presheaf of modules from
`Def_AlgebraicGeometry_OrderedAffineCoverCech`.

## Definitions and results

**Affine intersections.** Let `K` be an ordered affine cover of `V`.

- `isAffineOpen_inf_of_isSeparated` (theorem): if `π` is separated, the intersection of two affine
  opens of `V` is affine. The proof uses that the diagonal of a separated morphism is an affine
  morphism.
- `isAffineOpen_inter` (theorem): if `π` is separated, every finite intersection `K.inter s` is affine
  (induction on the length of `s`).
- `K.affineInter π s` is `K.inter s` as an element of `V.affineOpens`.

**Morphisms.** Let `F`, `G` be presheaves of modules over `π`.

- A `Hom F G` is a family of `R`-linear maps `app U : F.obj U → G.obj U`, one for each open `U`, that are
  `Γ(V, U)`-linear (`app_smul`) and commute with restrictions (`naturality`).
- An `AffHom F G` is the same data indexed only by the affine opens of `V`.
- A `SES F₁ F₂ F₃` is a pair of morphisms `inc : F₁ → F₂`, `proj : F₂ → F₃` such that on every open
  `U`, `inc` is injective, `proj` is surjective and the image of `inc` is the kernel of `proj`. So the
  sequence `0 → F₁(U) → F₂(U) → F₃(U) → 0` is exact on every open. `AffSES` is the same notion for
  affine-indexed morphisms, with exactness on every affine open.
- `Hom.appSections`, `AffHom.appSections`: the components as `Γ(V, U)`-linear maps. `Hom.id`,
  `Hom.comp`, `AffHom.id` and `AffHom.comp` are identities and composites, `Hom.toAffHom` restricts a
  morphism to affine opens, and `SES.toAffSES` does the same for short exact sequences.

**Induced maps on Čech cohomology.** Assume `π` separated, and let `K` be an ordered affine cover of `V`
and `φ : AffHom F G`.

- `φ.cochainMap K i : F.cochain K i → G.cochain K i` applies `φ` on each affine intersection
  `K.inter s`. `AffHom.cochainMap_comp_d` (theorem) says it commutes with the Čech differentials.
- `φ.kerMap K i` is its restriction to cocycles, `φ.H0Map K` the induced map `F.H0 K → G.H0 K`, and
  `φ.HSuccMap K i` the induced map `F.HSucc K i → G.HSucc K i` on higher Čech cohomology.

The remaining declarations are unfolding lemmas (`Hom.appSections_apply`, `Hom.naturality_apply`,
`Hom.id_app`, `Hom.comp_app`, `Hom.toAffHom_app`, the corresponding `AffHom` lemmas,
`AffHom.cochainMap_apply`, `AffHom.kerMap_coe`, `AffHom.HSuccMap_mk`).

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_OModulePresheafHom.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
