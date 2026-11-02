# `Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 5 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - FLT `p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.GoodReductionJacobian"`: namespace `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.GoodReductionJacobian` dropped.
- 2 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- Manual edit for Mathlib drift (FLT line 136, line 147 here): `(IsLocalRing.local_hom_TFAE φ).out 0 3` is replaced by `(IsLocalRing.local_hom_TFAE φ).out 1 4`. In the project's Mathlib, `List.TFAE.out` takes 1-indexed positions (FLT's Mathlib used 0-indexed ones); the list of `IsLocalRing.local_hom_TFAE` is unchanged, so both indices are increased by one and the proved implication is the same.
- Manual edit for Mathlib drift (FLT line 311, line 322 here): `(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R)` is replaced by `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)`. The constant `Ideal.bot_prime` no longer exists in the project's Mathlib; `Ideal.isPrime_bot` (Mathlib `RingTheory/Ideal/Prime.lean`) states the same fact, that `⊥` is a prime ideal of a nontrivial ring without zero divisors.
- Manual edit for Mathlib drift (FLT line 454, line 465 here): `(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R)` is replaced by `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)`. The constant `Ideal.bot_prime` no longer exists in the project's Mathlib; `Ideal.isPrime_bot` (Mathlib `RingTheory/Ideal/Prime.lean`) states the same fact, that `⊥` is a prime ideal of a nontrivial ring without zero divisors.
- No other change: the declarations and statements are the FLT ones, and the proofs are the FLT text except for the edits above.

## Content

Proof (Weil's extension argument). Namespace `FltWs29.DIAG`: dimension theory, ending with
`exists_specializes_diagonal_of_ringKrullDim_le_one_of_quotient_add_height`: if the stalk of
`T ×_R T` at a diagonal point `Δ(y)` satisfies the dimension formula `dim (O ⧸ 𝔔) + height 𝔔 = dim O`
and the kernel of `O_{T×T,Δ(y)} → O_{T,y}` needs exactly `dim O - dim O_{T,y}` generators, then
every generization `η` of `Δ(y)` with stalk of dimension `≤ 1` generizes `Δ(ξ)` for some `ξ ⤳ y`
with stalk of dimension `≤ 1`. Namespace `GoodReductionJacobian.RelativeGroupLaw.DENS`: density and
reducedness facts. Namespaces `...FltWs29.C3` and `C3b`: smooth schemes over `R` are reduced, the
difference map is the unit on the diagonal, and the difference map defines a rational map on an
irreducible component of `T ×_R T` into an affine open of `A`, defined at the diagonal points over
`V` (`exists_rationalMap_component_affine`). Namespace `DIAG` (lemmas `exists_nat_ringKrullDim_eq_of_isRegularLocalRing`,
`isCohenMacaulayOfDim_of_isRegularLocalRing`, `bprime_inputs`): the stalks at diagonal points are
regular, hence Cohen–Macaulay, which gives the two dimension inputs. `DIAG.B`: local noetherianity
and integrality of components, and affine neighbourhoods. `diag_assembly`: take the largest
difference extension `(W, d)` of
`GoodReductionJacobian.RelativeGroupLaw.exists_isGreatest_opens_difference_extension`. If a
diagonal point `Δ(y)` were outside `W`, then on its (open, integral) irreducible component the
rational map would not be defined at `Δ(y)`, so some generization `z` with stalk of dimension `≤ 1`
is outside its domain
(`AlgebraicGeometry.Scheme.RationalMap.exists_specializes_ringKrullDim_le_one_of_not_mem_domain`).
The dimension lemma gives `ξ` with `z ⤳ Δ(ξ)` and stalk of `ξ` of dimension `≤ 1`; then `ξ ∈ V`
(`AlgebraicGeometry.mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing`), so `Δ(ξ)` is in
the open domain and so is its generization `z`, a contradiction.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.exists_nat_of_add_natCast_eq`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.exists_nat_ringKrullDim_of_le`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.height_add_le_of_strictChain`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.exists_isPrime_map_le_height_le_one`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.coheight_fromSpecStalk`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.ringKrullDim_stalk_fromSpecStalk`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.exists_specializes_diagonal_of_ringKrullDim_le_one_of_quotient_add_height`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DENS.dense_of_generic_fibre_subset`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DENS.isReduced_pullback_of_smooth`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DENS.dense_inf_preimage_of_dense`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.C3.isReduced_of_smooth`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.C3.eq_one_of_mul_eq`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.C3.isDominant_homOfLE_inf`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.C3.diagonal_restrict_comp_eq_unit`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.C3b.exists_mem_specializes`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.C3b.exists_rationalMap_component_affine`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.exists_nat_ringKrullDim_eq_of_isRegularLocalRing`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.isCohenMacaulayOfDim_of_isRegularLocalRing`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.ringKrullDim_quotient_add_height_of_isRegularLocalRing`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.bprime_inputs`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.B.isLocallyNoetherian_of_locallyOfFiniteType_spec`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.B.isIntegral_and_isLocallyNoetherian_and_isIntegrallyClosed_of_isIrreducible`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.B.exists_isAffineOpen_forall_mem_of_isLocalRing`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.B.specializes_ι_of_specializes`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.B.specializes_of_specializes_ι`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.B.ringKrullDim_stalk_ι`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.B.ι_base_apply_mk`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.FltWs29.DIAG.diag_assembly`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library), `Langlands.AnthropicFLT.Definitions.Def_Patching_CohenMacaulayOfDim` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_IsRegularLocalRing_spanFinrank_ker_add_ringKrullDim_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_IsRegularLocalRing_depth_self_eq_ringKrullDim` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_RationalMap_exists_specializes_ringKrullDim_le_one_of_not_mem_domain` (same contribution).
Other imports: `Mathlib`.
