# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_comap_eq_of_isDirectLimit`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_comap_eq_of_isDirectLimit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands. Write `N` for this file's namespace `P2MW.S_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_comap_eq_of_isDirectLimit`. The `_root_.` prefix makes a name refer to the global namespace; inside `N` and its subnamespaces the plain name could resolve to a namespace of this file.
  - FLT line 14: `p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry N.AlgebraicGeometry TopologicalSpace Opposite"` becomes `open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite`. The namespace `N.AlgebraicGeometry` is omitted: at that point of the file it does not exist yet, and standard `open` rejects an unknown namespace, whereas `p2m_open` records the open declaration without checking. The file compiles without it.
  - FLT line 21: `p2m_export "AlgebraicGeometry" "…"` with 17 names becomes `export _root_.AlgebraicGeometry (…)` with the same names.
  - FLT line 23: `p2m_open "AlgebraicGeometry"` becomes `open _root_.AlgebraicGeometry`.
  - FLT line 25: `p2m_open "AlgebraicGeometry.Scheme.Modules"` becomes `open AlgebraicGeometry.Scheme.Modules`.
- No other change: the declarations, statements and proofs are the FLT text.

## Mathematical content

Setting shared by the FLT direct-limit lemmas. `ι` is a nonempty directed preorder, `(G j, φ j k)` is a
directed system of commutative rings in `Type u`, and the ring maps `g j : G j →+* R` satisfy FLT's
`IsDirectLimit` (ported module `Definitions.Def_Mathlib_Algebra_IsDirectLimit`): every element of `R` is
some `g j x`, two elements of stages with the same image in `R` become equal at a common later stage, and
`g k ∘ φ j k = g j`. For `i : ι`, `fX : X ⟶ Spec (G i)` is quasi-compact and quasi-separated
(`Spec (G i)` abbreviates `Spec (CommRingCat.of (G i))`). For `j ≥ i` write `X_j` for Mathlib's chosen
pullback `pullback fX (Spec.map (φ i j))` and `X_R` for `pullback fX (Spec.map (g i))`, with first
projections `p_j : X_j ⟶ X` and `p_R : X_R ⟶ X`. A morphism `c : X_R ⟶ X_j` *with the canonical
projections* is one with `c ≫ p_j = p_R` and `c ≫ (second projection of X_j) = (second projection of X_R) ≫
Spec.map (g j)`. By the universal property of the pullback there is exactly one such `c`; the statements
nevertheless quantify over all of them.

`solution` states: let `κ` be finite, let `W : κ → X.Opens` be quasi-compact opens whose preimages
`p_R⁻¹(W k)` cover `X_R`, and let `gc` be a unit cocycle (FLT `Scheme.Modules.UnitCocycle`, ported module
`Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle`) on these preimages. Then there are `j ≥ i` and a
unit cocycle `c` on the opens `p_j⁻¹(W k)` of `X_j` such that these opens cover `X_j` and, for every
`cX : X_R ⟶ X_j` with the canonical projections and all `a, b`, the pulled-back cocycle `c.comap cX` agrees
with `gc` on `p_R⁻¹(W a) ⊓ p_R⁻¹(W b)` (after restriction along the equality of the two descriptions of this
open).

Proof as implemented (namespace `AlgebraicGeometry.CocycleFil`). The helpers fix the canonical morphisms
`cc j : X_R ⟶ X_j` and `dd k l : X_l ⟶ X_k` (`cc_unique`: every morphism with the canonical projections is
`cc j`), the pullback of sections from a stage to `X_R` (`val`) and between stages (`push`), and their
compatibilities (`val_push`, `push_push`, restriction lemmas). `exists_val_eq`, `exists_push_eq` and
`exists_cover` restate `exists_app_eq_of_isCompact_of_isDirectLimit`,
`exists_app_eq_app_of_isCompact_of_isDirectLimit` and `exists_iSup_preimage_eq_top_of_isDirectLimit` in these
terms. In `main`: since `X` is quasi-separated, the opens `W a ⊓ W b` and `W a ⊓ W b ⊓ W c` are
quasi-compact. Each `gc.u a b` descends to a section over `p⁻¹(W a ⊓ W b)` at some stage, and all of them
are pushed to a common stage `j₁`. The identities `u a a = 1` and the cocycle identity on triple overlaps
hold after pullback to `X_R` (they hold for `gc`), so by `exists_push_eq` each of these finitely many
identities holds at some later stage; `exists_cover` gives a stage at which the `p⁻¹(W k)` cover. At a
common upper bound `js` the pushed sections satisfy the normalisation and the cocycle identity and pull back
to `gc`. In `solution` they are packaged as the cocycle `c`, and `cc_unique` identifies any `cX` with the
canonical projections with `cc js`.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- theorem `comp_eq`
- theorem `comp_eq'`
- theorem `spec_comp`
- theorem `spec_comp'`
- abbrev `XR`
- abbrev `XS`
- abbrev `prR`
- abbrev `prS`
- def `cc`
- theorem `cc_fst`
- theorem `cc_snd`
- theorem `cc_unique`
- def `dd`
- theorem `dd_fst`
- theorem `dd_snd`
- theorem `cc_dd`
- theorem `dd_dd`
- abbrev `castO`
- theorem `castO_castO`
- theorem `castO_rfl`
- theorem `pre_cc`
- theorem `pre_dd`
- theorem `app_castO`
- theorem `comp_app_apply`
- def `val`
- def `push`
- theorem `val_push`
- theorem `app_rO`
- theorem `rO_castO`
- theorem `val_rO`
- theorem `push_rO`
- theorem `push_push`
- theorem `castO_injective`
- theorem `exists_val_eq`
- theorem `exists_push_eq`
- theorem `exists_cover`
- abbrev `l12`
- abbrev `l23`
- abbrev `l13`
- theorem `main`
- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_app_eq_of_isCompact_of_isDirectLimit`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_app_eq_app_of_isCompact_of_isDirectLimit`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_iSup_preimage_eq_top_of_isDirectLimit`.
