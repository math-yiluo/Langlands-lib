# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift (FLT line 123, line 134 here): `(Localization.AtPrime q)).out 4 1).mp hprinc` is replaced by `(Localization.AtPrime q)).out 5 2).mp hprinc`. In the project's Mathlib, `List.TFAE.out` takes 1-indexed positions (FLT's Mathlib used 0-indexed ones); the list of `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain` is unchanged, so both indices are increased by one and the proved equivalence is the same.
- Manual edit for Mathlib drift (FLT line 475, line 486 here): `((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain V).out 1 0)` is replaced by `((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain V).out 2 1)`. In the project's Mathlib, `List.TFAE.out` takes 1-indexed positions (FLT's Mathlib used 0-indexed ones); the list of `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain` is unchanged, so both indices are increased by one and the proved equivalence is the same.
- Manual edit for Mathlib drift (FLT line 283, line 294 here): the FLT text
  `Nat.card_eq_fintype_card, Fintype.card_fin]  theorem exists_transcendental_finiteDimensional`
  is replaced by
  `ENat.card_eq_coe_fintype_card, Fintype.card_fin]   rfl  theorem exists_transcendental_finiteDimensional`.
  In the project's Mathlib, `MvPolynomial.ringKrullDim_of_isNoetherianRing` expresses the number of variables as `ENat.card σ` instead of `Nat.card σ`, so `Nat.card_eq_fintype_card` is replaced by `ENat.card_eq_coe_fintype_card` (Mathlib `SetTheory/Cardinal/Finite.lean`); the remaining goal, which differs only by the coercion through `ℕ∞`, is closed by `rfl`.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one`. Statement. `AlgebraicGeometry.exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one`: let `k` be algebraically
closed, `Y` separated and locally of finite type over `k`, `A` a finitely generated `k`-domain of Krull dimension
one, and `φ : Spec A ⟶ Y` over `k`. There are a smooth proper integral curve `C` over `k` (smooth of relative
dimension one), an open `U ⊆ C` and `ψ : U ⟶ Y` over `k` such that for every `k`-point `a` of `Spec A` there is a
`k`-point `p` of `U` with `p ≫ ψ = a ≫ φ`.

Proof. Let `L` be the fraction field of `A` and `C` a smooth proper model of `L` (ported
`AlgebraicCurve.CurveModel.nonempty_of_perfectField`; `L` has transcendence degree one, section `Ticket`, using the
ported `RingHom.finiteDimensional_adjoin_range_of_finite_of_forall_mem_range`). The generic point `Spec L ⟶ Spec A ⟶ Y`
spreads out to a partial map, hence a rational map `C ⇢ Y`; let `U` be its domain of definition and `ψ` the
morphism on it (section `Spread`). For a `k`-point `a` of `Spec A`, i.e. a maximal ideal `𝔪`, choose a place of
`L` whose valuation ring contains `A` and is centred at `𝔪` (section `Centre`, `exists_place_le_and_subset_nonunits`);
it is the local ring of a closed point `x` of `C` (local rings of `C` are valuation rings, section `LocalRings`). The
map `Spec 𝒪_{C,x} ⟶ Spec A ⟶ Y` extends the rational map at `x` (section `Extend`, separatedness of `Y`), so
`x ∈ U`, and the corresponding `k`-point `p` of `U` satisfies `p ≫ ψ = a ≫ φ`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.fromSpecStalkOfMem_eq_of_specializes`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.partialMap_fromSpecStalkOfMem_eq_of_specializes`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.partialMap_fromFunctionField_eq_of_mem`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.ofHom_algebraMap_stalk_functionField`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.mem_domain_of_valuationRing`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.valuationRing_of_surjective`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.valuationRing_localization_atPrime`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.isPrincipalIdealRing_mvPolynomial_fin_one`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.valuationRing_stalk`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.fromSpecStalk_genericPoint_comp_eq`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.isSeparated_of_over`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.existence_of_isProper`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.fromSpecStalk_comp_eq`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.exists_ltSeries_comap_eq_last`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.ringKrullDim_eq_of_isIntegral_of_injective`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.ringKrullDim_eq_of_ringHom_isIntegral_of_injective`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.ringKrullDim_mvPolynomial_fin`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.exists_transcendental_finiteDimensional`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.exists_place_le_and_subset_nonunits`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.isClosed_singleton_opens`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen.main`
- theorem `P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicCurve_CurveModel_nonempty_of_perfectField` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range` (same contribution).
Other imports: `Mathlib`.
