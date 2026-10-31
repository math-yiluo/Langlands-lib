# `Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation`

## Source

Port of `P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation.lean`
from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

Write `N` for the namespace
`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation`.

- Imports of FLT modules (`Definitions.*`, `Theorems.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib`
  is unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` is dropped, and its commands are replaced by standard Lean commands. The rest of the file,
  including every statement and proof, is the FLT text.
  - `p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian N.GoodReductionJacobian"`
    (FLT line 12) becomes `open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian`.
    The last namespace in the FLT list, `N.GoodReductionJacobian`, is omitted. At that point of the file it does not
    exist yet, and standard `open` rejects an unknown namespace, whereas `p2m_open` records the open declaration
    without checking. The file compiles without it: the declarations inside `N.GoodReductionJacobian` are written
    inside that namespace, and the final `solution` refers only to names that resolve the same way without it.
  - `p2m_export "GoodReductionJacobian" "<names>"` (inside `N.GoodReductionJacobian`) becomes
    `export _root_.GoodReductionJacobian (<names>)`, and `p2m_export "GoodReductionJacobian.RelativeGroupLaw" "<names>"`
    (inside `N.GoodReductionJacobian.RelativeGroupLaw`) becomes `export _root_.GoodReductionJacobian.RelativeGroupLaw (<names>)`,
    with the same lists of names. The `_root_` prefix is needed: inside a namespace of the same name, a plain
    `export GoodReductionJacobian (...)` would resolve to the enclosing namespace itself.
  - `p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"` (inside `GroupLawDescent`) becomes
    `open _root_.GoodReductionJacobian.RelativeGroupLaw _root_.GoodReductionJacobian`.
  - Each of the 15 `p2m_reactivate "<namespaces>"` commands becomes `open scoped <namespaces>`, with the same
    namespaces (mostly `N.GoodReductionJacobian.RelativeGroupLaw.GroupLawDescent.Dat`, whose `scoped simp` lemmas
    are used after a `section` or `namespace` is closed). `p2m_reactivate` first removes each namespace from the
    active scopes and then activates it again; `open scoped` only activates it. With this file the difference does
    not matter: the module compiles with 0 errors.
- The two long `p2m_export` lines are wrapped over two and three lines. With the 10-line header, the 3 inserted
  option lines and the dropped import, line numbers are 15 higher than in FLT from the `GroupLawDescent` namespace on.

## Contents

Declarations, with their original FLT names (no new definitions or statements are introduced). Everything is in
`N`. Apart from `solution`, everything is in `N.GoodReductionJacobian.RelativeGroupLaw.GroupLawDescent`. The file
proves FLT's descent of a relative group law to a finitely generated subalgebra. A group law on points is encoded as
morphisms between fibre products (`Dat`: multiplication `m`, unit `e`, inverse `ι`) satisfying the axioms `Laws`
as equalities of morphisms. These morphisms and equalities are descended to a finitely generated stage `T` with
FLT's noetherian approximation theorems `AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation`
and `AlgebraicGeometry.exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType`. Then a `RelativeGroupLaw` is
rebuilt from the descended data.

- section `Presentations`: abbrevs `W₂`, `w₂`, `W₃`, `w₃`, `Yb`, `fb`, `Q₂`, `Q₃`; defs `p₁`, `p₂`, `pair`, `q₁₂`, `q₃`,
  `triple`, `tW`; theorems `p₁_fst`, `p₁_snd`, `p₂_fst`, `p₂_snd`, `pair_aux₁`, `pair_aux₂`, `pair_fst_fst`,
  `pair_fst_snd`, `pair_snd`, `pair_p₁`, `pair_p₂`, `hom_ext₂`, `p₁_fb`, `p₂_fb`, `p₁_fb_eq_p₂_fb`, `pair_p₁_p₂`,
  `comp_pair`, `q₁₂_fst`, `q₁₂_snd`, `q₃_fst`, `q₃_snd`, `q₁₂_p₁_fb`, `q₁₂_p₂_fb`, `q₃_fb`, `triple_aux₁`,
  `triple_aux₂`, `triple_fst_fst`, `triple_fst_snd`, `triple_snd`, `triple_q₁₂`, `triple_q₃`, `hom_ext₃`,
  `triple_universal`, `comp_triple`, `tW_fst`, `tW_snd`, `eq_of_comp_tW_eq`, `tW_p₁`, `tW_p₂`, `tW_q₁₂`, `tW_q₃`,
  `tW_fb`, `pair_tW`, `triple_tW`
- section `Data`: structure `Dat` (fields `m`, `e`, `ι`, `hm`, `he`, `hι`); in namespace `Dat`: theorems `q₁₂_m_fb`,
  `p₂_m₂₃_fb`, `fb_e_fb`, `ι_fb`; defs `assocL`, `assocR`, `oneMulL`, `invMulL`, `unitC`, `commL`; theorems
  `assocL_fb`, `assocR_fb`, `oneMulL_fb`, `invMulL_fb`, `unitC_fb`, `commL_fb`; structure `Laws` (fields `assoc`,
  `one_mul`, `inv_mul`); theorems `res_m_aux`, `res_e_aux`, `res_ι_aux`; def `res`; theorems `res_m_fst`, `res_e_fst`,
  `res_ι_fst`, `res_m_tW`, `res_e_tW`, `res_ι_tW`, `assocL_tW`, `assocR_tW`, `oneMulL_tW`, `invMulL_tW`, `unitC_tW`,
  `commL_tW`, `m_tW`, `eq_of_tW`, `assoc_res`, `one_mul_res`, `inv_mul_res`, `Laws.res`, `comm_res`
- section `Congr`: theorem `pair_congr`
- section `OfLaw`: abbrev `qb`; defs `P₁`, `P₂`, `Pid`, `ofLaw`; theorems `P₁_val`, `P₂_val`, `Pid_val`, `mul_fb_eq`,
  `mul_val`, `one_val`, `inv_val`, `pair_P₁_P₂`, `ofLaw_laws`, `ofLaw_comm`
- section `OfDat`: defs `Dat.mulPt`, `Dat.onePt`, `Dat.invPt`, `Dat.toLaw`; theorems `Dat.mulPt_val`, `Dat.onePt_val`,
  `Dat.invPt_val`, `Dat.mulPt_assoc`, `Dat.onePt_mulPt`, `Dat.invPt_mulPt`, `Dat.mulPt_onePt`, `Dat.toLaw_mul_val`,
  `Dat.toLaw_one_val`, `Dat.toLaw_comm`
- section `Rebase`: theorem `isPullback_paste`; def `rebaseIso`; theorems `rebaseIso_hom_snd`, `rebaseIso_hom_fst`,
  `fst_eq_rebaseIso_hom_tW`
- section `TransComp`: theorems `tW_comp`, `tW_congr`
- namespace `Dat` (second block): theorems `eq_of`, `res_res`, `res_congr`, `assoc_res_iff`, `one_mul_res_iff`,
  `inv_mul_res_iff`, `comm_res_iff`
- section `Stages`: abbrevs `bT`, `bA`, `uA`, `uT`, `uF`; theorems `uA_bT`, `uT_bT`, `uA_uT`, `tW_snd_val`; def `flat`;
  theorems `le_flat`, `flat_fg`, `subset_flat`, `flat_mono`; def `flatHom`; theorems `uF_comp`, `exists_finset_of_fg`,
  `exists_tW_comp_eq`
- section `Final`: theorems `baseChange_mul_fst`, `exists_relativeGroupLaw`
- theorem `N.solution`: the statement of
  `GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation`,
  proved by `exists_relativeGroupLaw f L s`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange`,
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation`,
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType`
(the two theorem modules are part of the Library's port for scheme descent to finitely generated subalgebras).
