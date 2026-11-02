# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point`. Statement. `AlgebraicGeometry.IdealSheafData.comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point`:
in the construction of a Hilbert scheme `H ⟶ Spec S` for `f : X ⟶ Spec S`, given the functor-of-points
data `pt` (natural, surjective, injective up to isomorphism) and, for each affine open `V` of `H`,
the closed subscheme `ZV V` of `X ×_S V` given by the tautological point of `V`, together with an ideal
sheaf `I₀` on `X ×_S H` restricting to these on every `X ×_S V`: for every affine test
`s : Spec S' ⟶ Spec S` and every flat, locally finitely presented closed subscheme `Z ⊆ X ×_S Spec S'`,
the pullback of `I₀` along `X ×_S Spec S' ⟶ X ×_S H` (induced by the point `pt(Z)`) is the ideal of
`Z` (so `I₀` defines the universal family).

Proof (namespace `UScSol`). Section `bc`: base-change maps `pullback.map f g' f g (𝟙 X) a (𝟙 B)` are
pullbacks of `a`, open immersions when `a` is, with the expected ranges and composition rules. Section
`chart`: for an affine open `V` of `H`, `X ×_S V` is identified with the open `pr₂⁻¹ V` (`mV`, `eV`).
`ker_comp_iso_comap`; `idealSheafData_ext_of_openImmersions`: ideal sheaves agreeing after pullback
along a jointly surjective family of open immersions are equal. Section `transport`: base change of a
flat, finitely presented closed subscheme along a ring map, compatible with `pt` and with ideals
(`transport_model`). Main argument: cover `Spec S'` by basic opens `D(g)` mapping into affine opens
`V` of `H`; over `D(g)` the point factors through `Spec Γ(H, V)`, so by naturality of `pt` and
injectivity (`hinj`) the restriction of `Z` agrees with the base change of `ZV V`, whose ideal is
the pullback of `I₀`; conclude with `idealSheafData_ext_of_openImmersions`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol.bcMap_fst`
- theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol.bcMap_snd`
- theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol.isPullback_bcMap`
- theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol.isOpenImmersion_bcMap`
- theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol.range_bcMap`
- theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol.bcMap_comp`
- theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol.bcMap_congr`
- abbrev `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol.mV`
- scoped instance `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol.isOpenImmersion_mV`
- theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol.range_mV`
- def `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol.eV`
- theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol.eV_hom_ι`
- theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol.mV_snd`
- theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol.ker_comp_iso_comap`
- theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol.idealSheafData_ext_of_openImmersions`
- theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol.transport_model`
- theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library).
Other imports: none.
