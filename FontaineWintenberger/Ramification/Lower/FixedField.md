# Integers of intermediate fields of a finite Galois extension

Module `FontaineWintenberger.Ramification.Lower.FixedField`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field in the library's sense and `L/K` finite Galois. For an intermediate field `F`, the ring of integers used is the valuation ring of the spectral valuation of `L` restricted to `F`.

- `intermediate_spectral_isDiscreteValuationRing`, `intermediate_spectral_henselianLocalRing`: this ring is a discrete valuation ring and Henselian.
- `intermediate_spectral_exists_generator`: if the residue field of `K` is perfect, it is generated over `𝒪[K]` by one element.
- `fixedField_integer_moduleFinite`: for a subgroup `H` of `Gal(L/K)` with fixed field `F`, `spectralIntegerRing K L` is finite over the integers `A` of `F`.
- `fixedField_integer_isGaloisGroup`: `IsGaloisGroup H A B` for `B = spectralIntegerRing K L`; the integers of `F` are the `H`-invariants.

Three general instances are added, among them `IsGaloisGroup H (fixedField H) L`.

## What to watch for

The integers of `F` are not `spectralIntegerRing K F` but a valuation subring of `F` cut out by the valuation of `L`.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/FixedField.lean` (SHA-256 of the source file `fb9a09f7198e010b9a3a7ef9ddbf825d1e550004fbf90650244615c69faeab8a`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
