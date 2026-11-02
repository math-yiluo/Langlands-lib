# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 18 here); in 6 lines the replacements `Type` (universe 0) → `Type uz` (6 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf`. Statement. `AlgebraicGeometry.HilbertFunctor.exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf`
(saturation of Hilbert points in high degree): for a Hilbert polynomial `P` (of some homogeneous ideal
over some field) there is `D₀` such that for every `m ≥ D₀`, every ring `A` (universe `uz`), every
point `p` of the Hilbert functor over `A` with Hilbert function `hilbertFunctionOf n P m`, and every
form `F` of degree `d ≥ m`: if for each `i` some `Xᵢ^N F` lies in `p.I`, then `F ∈ p.I`.

Proof (namespace `SatHighReduce`; reduction to fields). Take `D₀` from the field case (ported
`HilbertFunctor.exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field`). Choose one `N`
for all `i`. The multiplication maps `phi I N d i : piece I d → piece I (N + d)` (by `Xᵢ^N`) kill the
class `x` of `F`. Lemma `eq_zero_of_forall_field`: for a map `Φ : M → M'` from a finite projective to
a flat module, if `Φ` is injective after every base change to a field then `Φ x = 0` forces `x = 0`.
Apply it to `Φ = (phi I N d i)ᵢ`: after base change to a field `k`, the pieces become those of the
extended point (ported `HilbertFunctor.exists_point_I_eq_map` and
`HilbertFunctor.exists_linearEquiv_baseChange_piece_map`), where the field case gives injectivity.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf.SatHighReduce.mulX`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf.SatHighReduce.mulX_apply_coe`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf.SatHighReduce.phi`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf.SatHighReduce.phi_mk`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf.SatHighReduce.mk_eq_zero_iff`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf.SatHighReduce.eq_zero_of_forall_field`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_map` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map` (same contribution).
Other imports: none.
