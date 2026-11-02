# `Langlands.AnthropicFLT.P2M.Sol.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift (FLT line 106, line 117 here): the FLT text
  `induction w with     | zero => rfl     | tmul a z => rw [Subsingleton.elim z 0, tmul_zero]`
  is replaced by
  `induction w with     | tmul a z => rw [Subsingleton.elim z 0, tmul_zero]`.
  In the project's Mathlib the induction principle of tensor products (`TensorProduct.inductionOn`, Mathlib `LinearAlgebra/TensorProduct/Defs.lean`) has only the cases `tmul` and `add`, so the case `zero` is removed.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range`. Statement. `Module.Flat.flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range`: for a bounded cochain complex of flat
modules that is exact in positive degrees, `ker d₀` is flat, and for every algebra `A`, `A ⊗ ker d₀ → ker (d₀ ⊗ A)` is
bijective and `C ⊗ A` is exact in positive degrees.

Proof. Descending induction from the top degree: the complex splits into short exact sequences
`0 → Zⁱ → Cⁱ → Zⁱ⁺¹ → 0` of cocycles (`Z`, `δ`, `exact_subtype_δ`, `δ_surjective`), and if `Zⁱ⁺¹` and `Cⁱ` are flat then
so is `Zⁱ` and the sequence stays exact after any base change (section `purity`, `lTensor_injective_of_flat_right`).
Section `complex`: assembling the base-changed short exact sequences gives exactness and the identification of the
kernel (`step`, `inv_all`, `range_lTensor_subtype_eq`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.C1Body.lTensor_injective_of_presentation`
- theorem `P2MW.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.C1Body.lTensor_injective_of_flat_right`
- abbrev `P2MW.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.C1Body.Z`
- def `P2MW.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.C1Body.δ`
- theorem `P2MW.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.C1Body.subtype_comp_δ`
- theorem `P2MW.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.C1Body.exact_subtype_δ`
- theorem `P2MW.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.C1Body.δ_surjective`
- def `P2MW.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.C1Body.Inv`
- theorem `P2MW.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.C1Body.inv_of_subsingleton`
- theorem `P2MW.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.C1Body.step`
- theorem `P2MW.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.C1Body.inv_all`
- theorem `P2MW.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.C1Body.range_lTensor_subtype_eq`
- theorem `P2MW.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech` (Library).
Other imports: `Mathlib`.
