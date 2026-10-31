# Every coherent sheaf on a noetherian separated scheme admits a dévissage step (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_hasDevissageStep`. Its
declarations live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_hasDevissageStep`.

## Statement

`solution : AlgebraicGeometry.OModulePresheaf.HasDevissageStep.{u}`. Spelled out (see
`Def_AlgebraicGeometry_OModulePresheafConstructions`): let `R` be a noetherian ring, `π : V ⟶ Spec R`
separated with `V` noetherian, and `F` a coherent, quasi-coherent presheaf of modules over `π`, supported
in a nonempty closed subset `Y` and annihilated on every affine open `U` by the vanishing ideal of `Y`
on `U`. Then `F` has a dévissage step for `Y`. That is, there are an irreducible closed `Z₀ ⊆ Y`, a
coherent quasi-coherent sheaf `H` on the integral subscheme `Z₀`, and an affine short exact sequence
`0 → i_*H → F → G₃ → 0` with `G₃` coherent, quasi-coherent and supported in a closed `Z₁ ⊊ Y`. The theorem
module `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_hasDevissageStep` states this as
`AlgebraicGeometry.OModulePresheaf.hasDevissageStep` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…AlgebraicGeometry.OModulePresheaf.G5B`.

1. **The `I`-torsion subpresheaf.** For an ideal sheaf `I`, `annIdealPMod π I F` is the subpresheaf of
   sections killed by `I` on every affine open below (`annIdealSub`, `mem_annIdealSub`,
   `annIdealSub_res`, `annIdealSub_Γsmul`; on affine opens this is `{x | I(U) x = 0}`,
   `annIdealSub_affine`). For the vanishing ideal of a closed `Z` it is supported in `Z`
   (`annIdealPMod_suppIn`, using `vanishingIdeal_ideal_eq_top`). It is quasi-coherent when `F` is and `V`
   is locally noetherian (`annIdealPMod_isQCF`, since `I(U)` is finitely generated).
2. **Restriction maps are bijective near `Z`.** Write `G₂ = annIdealPMod π I_Z F`. For affine opens
   `U' ⊆ U` with `(U \ U') ∩ Z = ∅`, restriction `G₂(U) → G₂(U')` is bijective (`G₂_res_bij`). This is
   first proved for basic opens `D(f) ⊇ U ∩ Z` (`G₂_res_bij_basicOpen`, `G₂_res_bij_basicOpen'`), where
   some `1 − c f` lies in `I_Z(U)`, so `c f` acts as the identity on `G₂` (`G₂_cf_id`).
3. **The sheaf `H` on the subscheme.** `G₂` is a module over the functions of the subscheme (`G₂_modZ`,
   `G₂_modZ_smul`). `annPullPMod π Z F` is the presheaf on the closed subscheme `Z` whose sections over
   an open `W` are the compatible families of sections of `G₂` over the affine opens `U` of `V` with
   `Z ∩ U ⊆ W` (`annPullIdx`, `annPullSub`, `G₂_modZW`, `G₂_modZW_smul`, `annPullSub_Γsmul`,
   `annPullΓmod`). By step 2, evaluation at `U` is a bijection from the sections of its pushforward over
   `U` to `G₂(U)` (`annPull_eval`, `preimage_le_hdisj`, `annPull_eval_bij`). So `i_*H ≅ G₂` on affine
   opens. Hence `i_*H` is coherent, quasi-coherent and supported in `Z` (`closedPushAnnPull_isCoherent`,
   `closedPushAnnPull_isQCF`, `closedPushAnnPull_suppIn`; `annPull_eval_Γsmul`, `annPull_eval_nat`).
4. **The quotient.** `quotAnnPMod π Z F = F / G₂` (`quotAnnΓmod`, `quotAnnΓmod_mk`) is coherent and
   quasi-coherent (`quotAnnPMod_isCoherent`, `quotAnnPMod_isQCF`). It vanishes on every affine open where
   `I_Z` already annihilates `F` (`quotAnnPMod_subsingleton`). `devSES` is the affine short exact sequence
   `0 → i_*H → F → F/G₂ → 0`.
5. **Choice of `Z₀` and `Z₁`** (`devStep'_exists`). Write the noetherian closed set `Y` as a finite union
   of irreducible closed sets and let `Z₀` be a maximal one. Put `Z₁ = closure (Y \ Z₀)`. Then `Z₁ ⊆ Y`,
   and `Z₀ ⊄ Z₁` by irreducibility and maximality of `Z₀`, so `Z₁ ⊊ Y`. The reduced subscheme on `Z₀` is
   integral (`Scheme.isIntegral_subscheme_vanishingIdeal`). On an affine open `U` disjoint from `Z₁`,
   `U ∩ Y = U ∩ Z₀`, so the vanishing ideals of `Y` and `Z₀` agree on `U`. Hence `F/G₂` vanishes there by
   the hypothesis on `F`, and `F/G₂` is supported in `Z₁`.
6. `hasDevissageStep` packages this, and `solution` is `hasDevissageStep`.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_hasDevissageStep.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` and
  `Theorems.Thm_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal` are renamed to the
  corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file
  then raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect: the first `p2m_open` becomes `open AlgebraicGeometry CategoryTheory
  TopologicalSpace Opposite` (dropping the `P2MW`-prefixed namespace, which does not exist at that
  point), the two `p2m_export` commands become `export _root_.AlgebraicGeometry (…)` and
  `export _root_.AlgebraicGeometry.OModulePresheaf (…)` with the same names, and the second `p2m_open`
  becomes `open _root_.AlgebraicGeometry.OModulePresheaf _root_.AlgebraicGeometry`. No declaration,
  statement or proof step changed.
