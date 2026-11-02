# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 14 here); in 72 lines the replacements `Type` (universe 0) → `Type uz` (69 places), `Scheme.{0}` → `Scheme.{uz}` (8 places), `Type` → `Type*` (a fresh universe; 1 place) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal`. Statement. `AlgebraicGeometry.Scheme.exists_isClosedImmersion_represents_of_forall_exists_ideal` (closed subfunctors):
let `X ⟶ Spec R` represent a functor `F` on `R`-algebras (natural bijections `pt A` between `F A` and the
`A`-points of `X` over `R`), and `W` a subfunctor condition which is closed: for every `s ∈ F A` there is an
ideal `𝔞` of `A` such that `W B (φ_* s)` holds iff `φ` kills `𝔞`. Then there are a closed immersion `ι : Z ⟶ X`
and bijections `ptZ A` between the elements of `F A` satisfying `W` and the `A`-points of `Z` over `R`,
compatible with `ι` and `pt`.

Proof (namespace `ClosedRep`). Section `Generalities`: sections killed on a cover vanish, ring maps from
morphisms of spectra over `R` (`algHomOfSpec`). Section `Setting`: the closure ideal `cl s` (the smallest
ideal of the closedness condition, unique by `ideal_unique`), `W ↔ cl = ⊥`, and its base-change behaviour
(`cl_map`). Sections `Charts`, `Sheaf`: on affine opens `D_a` of `X` the tautological points (`sU`, `resAlg`)
give ideals `J`, forming an ideal sheaf; section `Key`: a point of `X` factors through the closed
subscheme of `J` iff the corresponding element satisfies `W` (`local_iff`, `J_le_ker_iff`, `main`), and
`ptZ` is obtained from `pt` by restricting to these points.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.section_eq_zero_of_cover`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.algebraMap_comm_of_Spec`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.algHomOfSpec`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.algHomOfSpec_toRingHom`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.algHomOfSpec_apply`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.PtNatural`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.Closed`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.Fmap_id`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.Fmap_comp`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.eq_of_pt_eq`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.cl`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.cl_spec`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.ideal_unique`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.W_iff_cl_eq_bot`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.cl_map`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.ρ`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.algU`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.fromSpec_over`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.Da`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.isAffineOpen_Da`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.θ'`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.θ'_apply`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.algL`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.θ`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.fromSpec_Da`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.sU`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.pt_sU`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.resAlg`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.Fmap_resAlg_sU`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.J`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.local_iff`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.preimage_le_iSup`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.J_le_ker_iff`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep.main`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
