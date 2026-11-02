# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 3 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry`: namespace `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry` dropped.
- 4 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist`. Statement. `AlgebraicGeometry.ProjSpace.exists_forall_subsingleton_HSucc_twist` (Serre vanishing): for a finite
morphism `φ : X ⟶ ℙᴺ_A` over a noetherian ring `A` with `φ ≫ ProjSpace.π A N = π`, there is `m₀` such that
for all `m ≥ m₀` all higher Čech cohomology groups of the twist `φ^* 𝒪(m)` for the pulled-back standard
cover vanish.

Proof (namespace `AlgebraicGeometry.ProjSpace.Pack`). Index tuples of the pulled-back standard cover are
the tuples of `ProjSpaceCech.Idx N` (`idxEquiv`), with intersections the intersections of charts
(`inter_eq`). Via the ported `ProjSpace.exists_sec_shift_twistGradedModule_equiv`, the Čech cochains of
the twist are identified with the cochains of the shifted graded module `twistGradedModule φ π` in the
graded-module Čech complex (`chainFwd`, `chainBwd`, `chainEquiv`), compatibly with the differentials;
hence the cohomology groups are isomorphic (ported `LinearMap.nonempty_kerModRange_equiv_of_equiv_comm`).
The twist module contains a finitely generated graded module with saturated cokernel (ported
`ProjSpace.exists_isFG_hom_injective_saturated_twistGradedModule` and
`ProjSpaceCech.GradedModule.Hom.HMap_bijective_of_saturated`), whose higher cohomology vanishes after
large shifts (ported `ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.Pack.idxEquiv`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.Pack.img_nonempty`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.Pack.inter_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.Pack.twistRes_val`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.Pack.twistRes_twistRes`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.Pack.twistRes_self`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.Pack.chainFwd`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.Pack.chainBwd`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.Pack.chainFwd_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.Pack.chainBwd_apply`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.Pack.chainEquiv`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.Pack.chainEquiv_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.Pack.idxEquiv_face`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.Pack.chainEquiv_comm`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.Pack.nonempty_H_equiv_HSucc`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.TV.sat_shift`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry.ProjSpace.TV.exists_forall_subsingleton_HSucc_twist`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_Hom_HMap_bijective_of_saturated` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm` (same contribution).
Other imports: `Mathlib`.
