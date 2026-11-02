# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 19 here); in 2 lines the replacements `Type` (universe 0) → `Type uz` (1 place), `Scheme.{0}` → `Scheme.{uz}` (1 place) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero`. Statement. `AlgebraicGeometry.ProjSpace.forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero`:
if `dim piece J m = 0` for an ideal `J` over a field whose forms of degree `≥ m` are those vanishing on
`Z_k ⊆ ℙⁿ_k`, then for all `d ≥ m` the higher Čech cohomology of `𝒪_{Z_k}(d)` vanishes and every `H⁰`
class is given by a form of degree `d` (here `Z_k` is empty).

Proof. `dim piece J m = 0` means that all forms of degree `m`, in particular all `Xᵢ^m`, lie in `J`, hence
vanish on `Z_k`; on the chart `D₊(Xᵢ)` this makes `1 = Xᵢ^m / Xᵢ^m` vanish, so all chart sections are zero
and the twists have zero sections. Then all cohomology groups vanish and the zero form represents every
`H⁰` class.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution).
Other imports: `Mathlib`.
