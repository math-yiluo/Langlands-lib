# Residue Frobenius on completed p-adic Lubin–Tate levels

Module `Nyll.ClassFieldTheory.LubinTate.Padic.CompletedResidueFrobenius`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a prime `p` and a level `n`, the completed multiplicative Lubin–Tate level `padicCompletedLevelField p n` is totally ramified over the completed unramified coefficient field. This file deduces that the two residue fields are canonically isomorphic, and that every completed Frobenius lift indexed by a unit acts on the residue field of the level as the arithmetic Frobenius x ↦ xᵖ.

## Main results

- `padicCompletedLevel_residueDegree_eq_one`: the residue degree of the completed level over the completed unramified field is 1.
- `padicCompletedLevel_residueField_finrank_eq_one`: equivalently, the residue field of the level has dimension 1 over the residue field of the base.
- `padicCompletedLevel_residueMap_surjective`: the canonical map between the residue fields is surjective.
- `padicCompletedLevelResidueFieldEquiv`: the resulting ring isomorphism from the residue field of the base to that of the level, with simp lemmas saying it is the residue map and, on integral representatives, the residue of the inclusion of valuation rings.
- `padicCompletedUnitFrobeniusIntegerEquiv_residue_apply_eq_pow`: for a unit `u` of the valuation ring of ℚ_p, the automorphism `padicCompletedUnitFrobeniusIntegerEquiv p n u` of the valuation ring of the level induces x ↦ xᵖ on its residue field.

## Proof

Residue degree one follows from the equality of ramification index and degree proved for the completed level, through the criterion "residue degree one iff ramification index equals degree" for finite separable extensions; a residue field extension of dimension one has a bijective structure map. For the Frobenius statement, every residue class of the level comes from an element `a` of the Witt coefficient ring `padicCompletedUnramifiedWittRing p`. The Frobenius lift is compatible with the Witt-vector Frobenius on coefficients, and the Witt-vector Frobenius of `a` is congruent to `aᵖ` modulo the maximal ideal, since its constant coefficient is the p-th power of that of `a`.

## Points to watch

- Residue degree, residue maps and `residueFieldEquivOfSurjective` are the library's own notions for its discretely valued field structures, not Mathlib's.
- The Frobenius statement is about the residue action only; it does not identify the lift itself.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/CompletedResidueFrobenius.lean`: the Lean file is the source byte for byte (SHA-256 `dc9f8bfc7467e7075c839229803c50aa651fae139f4462c6112e79195d9428a0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
