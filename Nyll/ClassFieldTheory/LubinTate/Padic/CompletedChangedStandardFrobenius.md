# The changed-uniformizer Artin candidate is inverse Frobenius

Module `Nyll.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardFrobenius`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let D be the changed-uniformizer fixed field and M the standard–changed compositum at level n inside the completed p-adic level, with u a unit of ℤ_p. M is unramified over D, and the file identifies the relative Artin candidate of M/D, by the file's header the restriction of the inverse completed coefficient Frobenius (in the proof, the inverse of `padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹`, an automorphism of the integers of the completed level that depends on u⁻¹), with the inverse of the arithmetic Frobenius of M/D.

## Main result

- `padicCompletedChangedUniformizerRelativeArtinCandidate_eq_inverseArithmeticFrobenius`: `padicCompletedChangedUniformizerRelativeArtinCandidate p u n = (arithmeticFrobeniusOfUnramifiedValuation D M)⁻¹`.

## Proof

For an unramified extension, the map from the Galois group to automorphisms of the residue extension is injective, so it suffices to compare on residue fields. There, through a residue embedding of M, this automorphism acts as the p-th power map, which is also the residue arithmetic Frobenius of M/D.

## Watch for

The statement opens with a block of `let` bindings that equip D and M with the spectral norm, valuation, local-field structure, integral closure and unramifiedness from imported files; the equality is stated for these structures only.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/CompletedChangedStandardFrobenius.lean`: the Lean file is the source byte for byte (SHA-256 `d08db8d090080f10343606ccee9706fb93245de6b98a80473b238dc696ba93b8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
