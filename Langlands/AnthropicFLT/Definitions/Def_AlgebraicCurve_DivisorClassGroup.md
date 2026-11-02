# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- Manual edit for Mathlib drift (FLT line 372, line 384 here): `Finsupp.mapDomain_apply (MulAction.injective σ) D v` is replaced by `Finsupp.mapDomain_apply_of_injective (MulAction.injective σ) D v`. In the project's Mathlib the lemma `Finsupp.mapDomain_apply` for injective maps is named `Finsupp.mapDomain_apply_of_injective` (Mathlib `Data/Finsupp/Basic.lean`), with the same statement.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

Places, divisors and the degree-zero divisor class group of a function field (namespace
`AlgebraicCurve`), for a field extension `F / K`.

- `Place K F` (a structure): a valuation subring of `F` containing the image of `K`, different from
  `F`, and a principal ideal ring (hence a discrete valuation ring; instances `IsDiscreteValuationRing`,
  `Algebra K`, `IsScalarTower K _ F`); `Place.ext`, `toValuationSubring_injective`,
  `ValuationSubring.not_isField_of_ne_top`.
- For a place `v`: `ResidueField`, `deg v` (the `K`-dimension of the residue field), the class
  `FiniteResidue`, `heightOneSpectrum` (its maximal ideal), `adicValuation : Valuation F ℤᵐ⁰`, and the
  order `ord v f = -log (adicValuation f)` with its rules (`ord_zero`, `ord_one`, `ord_mul`,
  `ord_inv`, `ord_zpow`, units have order `0`, uniformizers order `1`, `ord_unit_smul_zpow`,
  `exists_unit_mul_zpow`).
- `Divisor K F := Place K F →₀ ℤ`, `Divisor.degree` (`∑ n_v deg v`; `degree_single`), the subgroups
  `degZero` (degree zero) and `principal` (divisors `(f)` with `D v = ord v f` for some `f ≠ 0`;
  `IsPrincipal`, `mem_principal`), the class `HasPrincipalDivisors` (every `f ≠ 0` has a divisor of
  degree `0`), `Pic`, `Pic0 = degZero / principal`, `Pic0.mk` (surjective, additive),
  `Pic0.torsion K F n` (the `n`-torsion) and `AbelJacobiCard K F p g` (the `pⁿ`-torsion of `Pic0` has
  `p^{2gn}` elements for all `n`).
- Galois action: `smulRingEquiv`, the action of `F ≃ₐ[K] F` on places (`MulAction`,
  `smul_toValuationSubring`, `ord_smul`, `smulResidueAlgEquiv`, `deg_smul`), on divisors
  (`DistribMulAction` by `Finsupp.comapDistribMulAction`; `smul_def`, `smul_single`,
  `smul_apply_smul`, `smul_apply`, `degree_smul`, preservation of `degZero` and `principal`) and on
  `Pic0` (`degZeroSMulHom`, `smul_mk`, `DistribMulAction`).
- `Place.ofHeightOneSpectrum w`: for a Dedekind domain `R` with fraction field `F` over `K`, the place
  given by the valuation of a height-one prime `w` (`isPrincipalIdealRing_valuationSubring`,
  `ofHeightOneSpectrum_toValuationSubring`).

## Declarations

Names, namespaces and statements are the FLT ones.

- structure `AlgebraicCurve.Place`
- theorem `ValuationSubring.not_isField_of_ne_top`
- theorem `AlgebraicCurve.Place.toValuationSubring_injective`
- theorem `AlgebraicCurve.Place.ext`
- anonymous instance of `IsPrincipalIdealRing v.toValuationSubring`
- anonymous instance of `IsDiscreteValuationRing v.toValuationSubring`
- anonymous instance of `Algebra K v.toValuationSubring`
- theorem `AlgebraicCurve.Place.coe_algebraMap`
- anonymous instance of `IsScalarTower K v.toValuationSubring F`
- abbrev `AlgebraicCurve.Place.ResidueField`
- def `AlgebraicCurve.Place.deg`
- class `AlgebraicCurve.Place.FiniteResidue`
- def `AlgebraicCurve.Place.heightOneSpectrum`
- theorem `AlgebraicCurve.Place.heightOneSpectrum_asIdeal`
- def `AlgebraicCurve.Place.adicValuation`
- theorem `AlgebraicCurve.Place.adicValuation_ne_zero`
- theorem `AlgebraicCurve.Place.adicValuation_coe`
- theorem `AlgebraicCurve.Place.adicValuation_coe_eq_one_iff`
- theorem `AlgebraicCurve.Place.adicValuation_coe_irreducible`
- def `AlgebraicCurve.Place.ord`
- theorem `AlgebraicCurve.Place.ord_zero`
- theorem `AlgebraicCurve.Place.ord_one`
- theorem `AlgebraicCurve.Place.ord_mul`
- theorem `AlgebraicCurve.Place.ord_inv`
- theorem `AlgebraicCurve.Place.ord_coe_unit`
- theorem `AlgebraicCurve.Place.ord_coe_irreducible`
- theorem `AlgebraicCurve.Place.ord_zpow`
- theorem `AlgebraicCurve.Place.ord_unit_smul_zpow`
- theorem `AlgebraicCurve.Place.exists_unit_mul_zpow`
- abbrev `AlgebraicCurve.Divisor`
- def `AlgebraicCurve.Divisor.degree`
- theorem `AlgebraicCurve.Divisor.degree_single`
- def `AlgebraicCurve.Divisor.degZero`
- theorem `AlgebraicCurve.Divisor.mem_degZero`
- def `AlgebraicCurve.Divisor.IsPrincipal`
- def `AlgebraicCurve.Divisor.principal`
- theorem `AlgebraicCurve.Divisor.mem_principal`
- class `AlgebraicCurve.HasPrincipalDivisors`
- abbrev `AlgebraicCurve.Pic`
- abbrev `AlgebraicCurve.Pic0`
- def `AlgebraicCurve.Pic0.mk`
- theorem `AlgebraicCurve.Pic0.mk_surjective`
- theorem `AlgebraicCurve.Pic0.mk_add`
- theorem `AlgebraicCurve.Pic0.mk_zero`
- def `AlgebraicCurve.Pic0.torsion`
- theorem `AlgebraicCurve.Pic0.mem_torsion`
- def `AlgebraicCurve.AbelJacobiCard`
- def `AlgebraicCurve.Place.smulRingEquiv`
- theorem `AlgebraicCurve.Place.coe_smulRingEquiv_apply`
- theorem `ValuationSubring.pointwise_smul_top`
- anonymous instance of `SMul (F ≃ₐ[K] F) (Place K F)`
- theorem `AlgebraicCurve.Place.smul_toValuationSubring`
- anonymous instance of `MulAction (F ≃ₐ[K] F) (Place K F)`
- theorem `AlgebraicCurve.Place.ord_smul`
- def `AlgebraicCurve.Place.smulResidueAlgEquiv`
- theorem `AlgebraicCurve.Place.deg_smul`
- anonymous instance of `DistribMulAction (F ≃ₐ[K] F) (Divisor K F)`
- theorem `AlgebraicCurve.Divisor.smul_def`
- theorem `AlgebraicCurve.Divisor.smul_single`
- theorem `AlgebraicCurve.Divisor.smul_apply_smul`
- theorem `AlgebraicCurve.Divisor.smul_apply`
- theorem `AlgebraicCurve.Divisor.degree_smul`
- theorem `AlgebraicCurve.Divisor.smul_mem_degZero`
- theorem `AlgebraicCurve.Divisor.smul_mem_principal`
- def `AlgebraicCurve.Pic0.degZeroSMulHom`
- theorem `AlgebraicCurve.Pic0.coe_degZeroSMulHom`
- anonymous instance of `SMul (F ≃ₐ[K] F) (Pic0 K F)`
- theorem `AlgebraicCurve.Pic0.smul_mk`
- anonymous instance of `DistribMulAction (F ≃ₐ[K] F) (Pic0 K F)`
- theorem `AlgebraicCurve.Place.isPrincipalIdealRing_valuationSubring`
- def `AlgebraicCurve.Place.ofHeightOneSpectrum`
- theorem `AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib.RingTheory.DedekindDomain.AdicValuation`, `Mathlib.RingTheory.Valuation.Discrete.Basic`, `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`, `Mathlib.RingTheory.LocalRing.ResidueField.Basic`, `Mathlib.Data.Finsupp.SMul`, `Mathlib.Algebra.BigOperators.Finsupp.Basic`, `Mathlib.Algebra.Module.Torsion.Basic`, `Mathlib.Algebra.Ring.Subring.Pointwise`, `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, `Mathlib.RingTheory.Bezout`.
