# Inertia over a base with finite residue field

Module `FontaineWintenberger.Ramification.Lower.FiniteResidue`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field in the library's sense whose residue field `𝓀[K]` is finite, and `L/K` a finite Galois extension with ring of integers `spectralIntegerRing K L`.

- `spectralIntegerRing_residueField_finite` (an instance): the residue field of `L` is finite.
- `isCyclic_localResidueGaloisHom_range`: the image of `Gal(L/K)` in the automorphism group of the residue field extension, under `localResidueGaloisHom`, is cyclic.
- `commutatorElement_mem_lowerRamificationGroup_zero`: every commutator `⁅g, h⁆` in `Gal(L/K)` lies in the zeroth lower ramification group.

The last statement holds because the zeroth lower group is the kernel of `localResidueGaloisHom` (`ker_localResidueGaloisHom`, from an earlier file), and the Galois group of an extension of finite fields is cyclic, hence commutative.

## What to watch for

The finiteness of the residue field is essential here; most of the surrounding files assume only a perfect residue field.

## References

Serre, *Local Fields*, Chapter IV, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/FiniteResidue.lean` (SHA-256 of the source file `55f6baf5ec6bb737f4071d76cc2fa47d938b66fa8d0870ab1111f4d477c102a0`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
