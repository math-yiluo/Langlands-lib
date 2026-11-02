# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces (FLT line 123, line 134 here), which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `ProBasisGC4`).

- Section `Chart`: for an affine open chart `uC : Spec C ⟶ X` (`chartAlgebra` makes `C` an
  `R`-algebra), `chartMap` is the open immersion `Spec (C ⊗[R] T) ⟶ X ×_{Spec R} Spec T`
  (`pullbackSpecIso`); `chartMap_fst`, `chartMap_snd` compute its projections,
  `chartMap_isOpenImmersion` (a scoped instance) and `mem_range_chartMap` describe its range.
- Section `Transition`: `τ` is the algebra map `C ⊗[R] S → C ⊗[R] A`, and `chartMap_comp_q`
  identifies `q` on the chart with `Spec τ`.
- `mem_preimage_basicOpen`: preimages of basic opens under `Spec.map`.
- `solution`: choose an affine chart of `X` containing the image of `w`, and a basic open
  `D(s) ⊆ chartMap⁻¹ U` of `Spec (C ⊗[R] A)` containing the corresponding point. Write `s` as a
  finite sum of pure tensors (`TensorProduct.exists_finset`); by directedness all its `A`-factors
  lie in one `S i`, giving `s'` in `C ⊗[R] S i` with `τ s' = s`. Then `W` is the image of `D(s')`
  under `chartMap`; injectivity of the open immersion `chartMap` gives `(q i)⁻¹ W ⊆ U`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra.ProBasisGC4.chartAlgebra`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra.ProBasisGC4.comp_eq_SpecMap`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra.ProBasisGC4.chartMap`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra.ProBasisGC4.chartMap_fst`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra.ProBasisGC4.chartMap_snd`
- scoped instance `P2MW.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra.ProBasisGC4.chartMap_isOpenImmersion`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra.ProBasisGC4.mem_range_chartMap`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra.ProBasisGC4.τ`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra.ProBasisGC4.chartMap_comp_q`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra.ProBasisGC4.mem_preimage_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra.solution`

## Dependencies

Ported FLT modules imported: none.
All modules also import `Mathlib`.
