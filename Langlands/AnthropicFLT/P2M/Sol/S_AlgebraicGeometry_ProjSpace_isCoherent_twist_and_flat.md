# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 1 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names. The command `export _root_.P2mTwistCohFlat (flat)` is dropped; see the port edit below.
- Port edit replacing a `P2M.Util` alias (FLT line 95, line 105 here): `⟨fun U => finite π φ m U, fun U => flat π φ m U⟩` is replaced by `⟨fun U => finite π φ m U, fun U => _root_.P2mTwistCohFlat.flat π φ m U⟩`. FLT `p2m_export "P2mTwistCohFlat" "flat"` aliases the private declaration(s) `_root_.P2mTwistCohFlat.`, `_root_.flat.` (declared earlier in the file) into the current namespace. Standard `export` cannot do this: `P2mTwistCohFlat` contains only private declarations and is not a registered namespace (`unknown namespace`). The command is dropped, and the uses of the alias are written with the full name of the private declaration, which denotes the same declaration.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat`. Statement. `AlgebraicGeometry.ProjSpace.isCoherent_twist_and_flat`: for `π : X ⟶ Spec A` separated and an affine
morphism `φ : X ⟶ ℙᴺ_A`, the twist `φ^* 𝒪(m)` is coherent, and its sections over every affine open `U`
are flat over `Γ(X, U)`.

Proof. On an affine open `U`, the charts `U ∩ φ⁻¹ D₊(Xᵢ)` are affine and cover `U`; on each the twist is
free of rank one (ported `ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart`). The twist is
quasi-coherent (ported `ProjSpace.isQuasicoherent_twist`), so its sections over `U` restrict to
localizations on the basic opens of a finite cover (ported
`OModulePresheaf.isLocalizedModule_res_of_isQuasicoherent`). A module that becomes free of rank one on a
finite cover by basic opens is finitely generated and flat (local criteria).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat.P2mTwistCohFlat.smallFuns`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat.P2mTwistCohFlat.span_smallFuns`
- scoped instance `P2MW.S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat.P2mTwistCohFlat.moduleU`
- scoped instance `P2MW.S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat.P2mTwistCohFlat.isScalarTower_U`
- scoped instance `P2MW.S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat.P2mTwistCohFlat.isLocalization_U`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat.P2mTwistCohFlat.isLocalizedModule_res`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat.P2mTwistCohFlat.finite_local`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat.P2mTwistCohFlat.flat_local`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat.P2mTwistCohFlat.finite`
- private theorem `P2mTwistCohFlat.flat`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat.P2mTwistCohFlat.main`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafSectionsLinearRes` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent` (same contribution).
Other imports: `Mathlib`.
