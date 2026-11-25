# Unit quotients O^*/U^n and the graded pieces U^n/U^(n+1)

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a field with a chosen complete discrete valuation (the library's `CompleteDVF`), valuation ring O, maximal ideal 𝔪, residue field k and higher principal unit groups U^n = 1 + 𝔪^n for n ≥ 1 and U^0 = O^*. The file describes O^*/U^n through the units of O/𝔪^n, identifies each graded piece U^n/U^(n+1) (n ≥ 1) with 𝔪^n/𝔪^(n+1) and with k, counts U¹/U^n when k is finite, and continues the action of valuation-ring-preserving field automorphisms on these quotients.

## Main definitions and results

- `unitsModOne_mk_eq_iff_residue_eq`: two units have the same class in O^*/U¹ iff they have the same residue.
- `quotientUnitHom F n`: reduction O^* → (O/𝔪^n)^*. Its kernel is U^n (`quotientUnitHom_ker_eq`), it is surjective for n ≥ 1, and `unitsModHigherPrincipalUnitGroupEquivQuotientUnits` gives O^*/U^n ≃ (O/𝔪^n)^* for n ≥ 1.
- Finiteness, for finite k: O/𝔪^n, O^*/U^n and every U^m/U^n are finite (lemmas and instances); `card_unitsModHigherPrincipalUnitGroup_eq_quotientUnits` equates the orders of O^*/U^n and (O/𝔪^n)^* for n ≥ 1.
- `toPrincipalUnitFiltration`: the filtration (U^n) packaged in the library's `AntitoneSubgroupFiltration` interface.
- `principalUnitSuccQuot F n`: the quotient U^n/U^(n+1), with quotient map, lift, induction principle and comparison with the filtration's graded piece.
- `principalUnitSuccQuotOfIdealPow`: for n ≥ 1, a ∈ 𝔪^n ↦ class of 1 + a. It depends only on a modulo 𝔪^(n+1), is trivial exactly on 𝔪^(n+1), and is additive.
- `maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot`: the resulting additive isomorphism 𝔪^n/𝔪^(n+1) ≃ U^n/U^(n+1), n ≥ 1.
- `principalUnitSuccQuotAddEquivResidueOfUniformizer`: given a uniformizer π, U^n/U^(n+1) ≃ k additively for n ≥ 1, sending the class of 1 + rπ^n to the residue of r (`..._coord`, `..._symm_residue`).
- `card_principalUnitSubquotient_one_eq_residue_pow_of_uniformizer`: given a uniformizer, for finite k and n ≥ 1, U¹/U^n has #k^(n−1) elements.
- Automorphisms: for `e : K ≃+* K` preserving O, `quotientMaximalIdealPowRingEquivOfPreserves` is the induced automorphism of O/𝔪^n, compatible with unit reduction; the induced automorphism of O^*/U^n preserves the image of each U^m, m ≤ n; and if `e` is trivial on k, then q⁻¹·e(q) lies in the image of U¹ for every q in O^*/U^n.

## Proofs

Surjectivity of unit reduction uses that O is local. Additivity of a ↦ 1 + a modulo U^(n+1) comes from (1 + a)(1 + b) = 1 + a + b + ab with ab ∈ 𝔪^(2n) ⊆ 𝔪^(n+1). The count of U¹/U^n multiplies the orders of the graded pieces, using the library's product formula for filtrations.

## Points to note

- The identifications with k depend on a chosen uniformizer and need n ≥ 1.
- The count is for U¹/U^n, giving #k^(n−1); other files use U¹/U^(n+1) with #k^n.
- The last lemma, `finite_principalUnitSubgroupClassInQuotient_of_finite_residue`, concerns the image of U^i in O^*/U^(i+1), which is a copy of U^i/U^(i+1).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/Core.lean`: the Lean file is the source byte for byte (SHA-256 `b913f9211072d3b7c1634907c76f88f9d92b245c274d3f8875479bd3b7789e6e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
