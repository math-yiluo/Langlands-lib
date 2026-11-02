# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Places of rational function fields and transport of places (namespace `AlgebraicCurve`).

- Section `Place` (general `F / K`): `adicValuation_valuationSubring` (the valuation subring of the
  adic valuation of `v` is `v`), `mem_iff_adicValuation_le_one`, instances
  `IsRankOneDiscrete` and `IsTrivialOn K` for `v.adicValuation`,
  `isEquiv_adicValuation_of_valuationSubring_eq`, `mem_maximalIdeal_iff_adicValuation_lt_one`,
  `ord_eq_zero_iff_adicValuation_eq_one`; for a Dedekind domain `R` with fraction field `F`:
  `isEquiv_adicValuation_ofHeightOneSpectrum`, `ofHeightOneSpectrum_injective`,
  `ord_ofHeightOneSpectrum_ne_zero_iff` (`ord ≠ 0` at `w` iff `q ∈ w`).
- `RationalFunctionField` (for `RatFunc K`): `heightOneSpectrumOfIrreducible hp` (the prime `(p)` of
  `K[X]` for irreducible `p`), `exists_irreducible_span`, `finitePlace K hp`; the residue map
  `residueOfHeightOneSpectrum K w : K[X] → κ(v_w)` with kernel `w` and surjective, the `K`-algebra
  isomorphism `residueFieldEquivOfHeightOneSpectrum : K[X] ⧸ w ≃ₐ[K] κ(v_w)`, so
  `deg (v_w) = deg p` for `w = (p)` (`deg_ofHeightOneSpectrum`, `deg_finitePlace`);
  `placeOfPoint K a` (the place of `X - a`), injective (`placeOfPoint_injective`), of degree `1`
  (`deg_placeOfPoint`).
- Section `Congr`: for a ring isomorphism `e : F ≃+* F'` compatible with the maps from `K`,
  `comapSymmRingEquiv`, `congrRingEquiv e he v` (the transported place, with `ord` preserved,
  `ord_congrRingEquiv`), `congrResidueAlgEquiv`, `deg_congrRingEquiv`, and the bijection
  `congrEquiv e he : Place K F ≃ Place K F'`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicCurve.Place.adicValuation_valuationSubring`
- theorem `AlgebraicCurve.Place.mem_iff_adicValuation_le_one`
- anonymous instance of `v.adicValuation.IsRankOneDiscrete`
- anonymous instance of `v.adicValuation.IsTrivialOn K`
- theorem `AlgebraicCurve.Place.isEquiv_adicValuation_of_valuationSubring_eq`
- theorem `AlgebraicCurve.Place.mem_maximalIdeal_iff_adicValuation_lt_one`
- theorem `AlgebraicCurve.Place.ord_eq_zero_iff_adicValuation_eq_one`
- theorem `AlgebraicCurve.Place.isEquiv_adicValuation_ofHeightOneSpectrum`
- theorem `AlgebraicCurve.Place.ofHeightOneSpectrum_injective`
- theorem `AlgebraicCurve.Place.ord_ofHeightOneSpectrum_ne_zero_iff`
- def `AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible`
- theorem `AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal`
- theorem `AlgebraicCurve.RationalFunctionField.exists_irreducible_span`
- def `AlgebraicCurve.RationalFunctionField.finitePlace`
- theorem `AlgebraicCurve.RationalFunctionField.finitePlace_def`
- theorem `AlgebraicCurve.RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum`
- def `AlgebraicCurve.RationalFunctionField.residueOfHeightOneSpectrum`
- theorem `AlgebraicCurve.RationalFunctionField.residueOfHeightOneSpectrum_apply`
- theorem `AlgebraicCurve.RationalFunctionField.ker_residueOfHeightOneSpectrum`
- theorem `AlgebraicCurve.RationalFunctionField.surjective_residueOfHeightOneSpectrum`
- def `AlgebraicCurve.RationalFunctionField.residueFieldEquivOfHeightOneSpectrum`
- theorem `AlgebraicCurve.RationalFunctionField.deg_ofHeightOneSpectrum`
- theorem `AlgebraicCurve.RationalFunctionField.deg_finitePlace`
- def `AlgebraicCurve.RationalFunctionField.placeOfPoint`
- theorem `AlgebraicCurve.RationalFunctionField.placeOfPoint_def`
- theorem `AlgebraicCurve.RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum`
- theorem `AlgebraicCurve.RationalFunctionField.placeOfPoint_injective`
- theorem `AlgebraicCurve.RationalFunctionField.deg_placeOfPoint`
- def `AlgebraicCurve.Place.comapSymmRingEquiv`
- theorem `AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply`
- theorem `AlgebraicCurve.Place.symm_algebraMap_comm`
- def `AlgebraicCurve.Place.congrRingEquiv`
- theorem `AlgebraicCurve.Place.congrRingEquiv_toValuationSubring`
- theorem `AlgebraicCurve.Place.ord_congrRingEquiv`
- def `AlgebraicCurve.Place.congrResidueAlgEquiv`
- theorem `AlgebraicCurve.Place.deg_congrRingEquiv`
- def `AlgebraicCurve.Place.congrEquiv`
- theorem `AlgebraicCurve.Place.congrEquiv_apply`
- theorem `AlgebraicCurve.Place.congrEquiv_symm_apply`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup` (same contribution).
Other imports: `Mathlib`.
