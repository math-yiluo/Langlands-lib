# `Langlands.AnthropicFLT.Definitions.Def_LinearMap_ExtPushout`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_LinearMap_ExtPushout.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Let `B` be a commutative ring, `p : B^r → M` a `B`-linear map and `δ : ker p → N` a `B`-linear map. This module
defines the pushout extension `ExtPushout p δ`, the extension of `M` by `N` obtained by pushing out
`0 → ker p → B^r → M` along `δ` (the Yoneda description of an `Ext¹` class):

- `extPushoutRel p δ` is the submodule of `N × B^r` of pairs `(δ s, −s)` for `s ∈ ker p`
  (`mem_extPushoutRel_iff`), and `ExtPushout p δ` is the quotient `(N × B^r) / extPushoutRel p δ`.
- `ExtPushout.mk` is the quotient map (`mk_apply`, `mk_surjective`, `mk_eq_zero_iff`), `inl : N → ExtPushout` and
  `inr : B^r → ExtPushout` its restrictions to the factors (`inl_apply`, `inr_apply`, `mk_eq_inl_add_inr`), with
  `inr s = inl (δ s)` for `s ∈ ker p` (`inr_coe`).
- `proj : ExtPushout → M` is induced by `(n, v) ↦ p v` (`proj_mk`, `proj_inl`, `proj_inr`, `proj_comp_inl`,
  `proj_comp_inr`); `inl` is injective, `proj` is surjective when `p` is, and `range inl = ker proj`
  (`inl_injective`, `proj_surjective`, `range_inl_eq_ker_proj`), so `0 → N → ExtPushout → M → 0` is exact.
- Universal property: maps `f : N → Q` and `g : B^r → Q` with `f ∘ δ = g` on `ker p` induce
  `lift p δ f g h : ExtPushout → Q` (`lift_mk`, `lift_inl`, `lift_inr`), and maps out of `ExtPushout` are determined
  by their composites with `inl` and `inr` (`hom_ext`).

## Declarations

Names, namespaces and statements are the FLT ones.

- def `LinearMap.extPushoutRel`
- theorem `LinearMap.mem_extPushoutRel_iff`
- abbrev `LinearMap.ExtPushout`
- def `LinearMap.ExtPushout.mk`
- theorem `LinearMap.ExtPushout.mk_apply`
- theorem `LinearMap.ExtPushout.mk_surjective`
- theorem `LinearMap.ExtPushout.mk_eq_zero_iff`
- def `LinearMap.ExtPushout.inl`
- def `LinearMap.ExtPushout.inr`
- theorem `LinearMap.ExtPushout.inl_apply`
- theorem `LinearMap.ExtPushout.inr_apply`
- theorem `LinearMap.ExtPushout.mk_eq_inl_add_inr`
- theorem `LinearMap.ExtPushout.inr_coe`
- def `LinearMap.ExtPushout.proj`
- theorem `LinearMap.ExtPushout.proj_mk`
- theorem `LinearMap.ExtPushout.proj_inl`
- theorem `LinearMap.ExtPushout.proj_inr`
- theorem `LinearMap.ExtPushout.proj_comp_inl`
- theorem `LinearMap.ExtPushout.proj_comp_inr`
- theorem `LinearMap.ExtPushout.inl_injective`
- theorem `LinearMap.ExtPushout.proj_surjective`
- theorem `LinearMap.ExtPushout.range_inl_eq_ker_proj`
- def `LinearMap.ExtPushout.lift`
- theorem `LinearMap.ExtPushout.lift_mk`
- theorem `LinearMap.ExtPushout.lift_inl`
- theorem `LinearMap.ExtPushout.lift_inr`
- theorem `LinearMap.ExtPushout.hom_ext`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
