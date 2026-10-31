# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper`

Ported for task `ab019f66-cba5-4921-aa53-b9cfb52e5456` (descent of geometric connectedness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit (2 declarations): FLT declares, inside namespace
  `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L`,
  `private abbrev _root_.SolML0L.ι …` and `private noncomputable def _root_.SolML0L.alg …` (private
  declarations in the root namespace `SolML0L`), each followed by `p2m_export "SolML0L" "ι"`
  (resp. `"alg"`), an FLT command from `P2M.Util` that adds an alias in the current namespace. Here
  they are declared as `private abbrev ι …` and `private noncomputable def alg …` directly in the
  current namespace, without `_root_` and without the export (the same treatment as `UnionModel.ι`
  in the Library module
  `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation`). The bodies are unchanged; the names `ι` and `alg` resolve inside the namespace as
  before, and the module no longer adds root-namespace declarations `SolML0L.ι`, `SolML0L.alg`.
- No other change: the declarations, statements and proofs are the FLT text. The FLT `attribute [-…]`
  lines after the namespace header (which locally deactivate instances and simp lemmas declared in
  imported FLT modules) are kept unchanged.

## Content

Proof. Write `X_I = P ×_A Spec (A ⧸ I)` with closed immersion `ι : X_I ⟶ P`.

- `SolML0L`: for an affine open `U` of `P`, the kernel of `Γ(P, U) → Γ(X_I, ι⁻¹U)` is the extension
  of `I` (`ker_ι_app`, using the pushout description `ker_eq_map_and_surjective_of_isPushout` of
  namespace `SolML0P`) and the map is surjective. `LiftsAt I U t c` says that `c ∈ Γ(P, U)` restricts
  to `t ∈ Γ(X_I, ⊤)` on `ι⁻¹U`; lifts exist over affine opens and are compatible with ring
  operations and restriction, and a section of `X_I` is determined by its local lifts on a cover.
- `SolML0C`: a finite ordered affine open cover `cover P` of the (quasi-compact) scheme `P`; global
  sections of `P` are exactly the Čech `0`-cocycles of the structure presheaf for this cover
  (`toCochain` is injective and its image is the kernel of `d`, `toCochain_surjective`).
- `main`: take `c` from `OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_of_isProper` for this
  cover (properness gives separatedness, so intersections of affines are affine). Given a global
  section `t` of `X_{I^{n+c}}`, lift it on each affine of the cover to a `0`-cochain `w`; then `d w`
  has entries in `I^{n+c}`, so there is `w'` with entries in `I^n` and `d w' = d w`. Hence `w - w'` is
  a cocycle, i.e. a global section `a` of `P`, and `a` and `t` have the same restriction to
  `X_{I^n}`. `solution` applies `main`.

## Declarations

Names, namespaces and statements are the FLT ones (except for the two private declarations of the manual edit above). Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0P.ker_eq_map_and_surjective_of_isPushout`
- abbrev `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.quot`
- abbrev `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.XI`
- private abbrev `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.ι`
- abbrev `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.pI`
- private def `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.alg`
- def `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.φ`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.alg_map`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.appLE_top_top`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.appLE_congr_hom`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.ker_ι_app`
- def `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.LiftsAt`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.LiftsAt.exists`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.LiftsAt.zero`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.LiftsAt.add`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.LiftsAt.sub`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.LiftsAt.mul`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.LiftsAt.sub_mem_iff`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.LiftsAt.mem_iff_of_zero`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.LiftsAt.restrict`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.LiftsAt.alg`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.eq_zero_of_forall_affine`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.eq_zero_of_forall_liftsAt`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.eq_of_forall_liftsAt`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.presheaf_map_congr`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.LiftsAt.of_appTop`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.LiftsAt.trans_of`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0L.eq_of_forall_liftsAt_cover`
- def `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.cover`
- def `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.vtx`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.idx0_eq_vtx`
- def `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.edge`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.face_edge_zero`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.face_edge_one`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.inter_edge_le_left`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.inter_edge_le_right`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.inf_vtx_le_inter_edge`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.U_le_inter_vtx`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.iSup_inter_vtx`
- def `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.toCochain`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.toCochain_apply`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.d_toCochain`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.range_toCochain_le`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.toCochain_injective`
- lemma `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.toCochain_surjective`
- theorem `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0.main`
- theorem `P2MW.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library, ported by task `69435287-9f1e-4abd-8483-5e65ff23668a`), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper` (same contribution).
All modules also import `Mathlib`.
