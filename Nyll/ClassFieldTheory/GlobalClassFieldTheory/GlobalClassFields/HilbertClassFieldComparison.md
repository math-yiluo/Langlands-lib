# The big and small Hilbert class fields compared

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A number field K has two Hilbert class fields. The big one, the narrow Hilbert class field, has norm group with quotient the narrow class group Cl⁺(K). The small one has quotient the ordinary class group Cl(K). This file identifies the natural map between the two reciprocity quotients with the map Cl⁺(K) → Cl(K) and computes its kernel. The kernel is the group of real signs modulo the signs of global units.

## Main definitions and results

- `bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk` and `smallHilbertClassFieldQuotientEquivClassGroup_mk`: on an idèle representative, the imported isomorphisms with Cl⁺(K) and Cl(K) are the obvious maps.
- `bigToSmallHilbertQuotient_compatible_with_narrowToClassGroup` and `bigToSmallHilbertQuotient_compatibility`: under these isomorphisms, the transition between the two quotients is `RayClass.narrowToClassGroup`.
- `realSignToBigHilbertClassFieldQuotient`: the map from the real sign group (`RayClass.realSignGroup K`) to the big Hilbert quotient, through Cl⁺(K).
- `hilbertClassFieldSign_exact_sequence`: the sequence 1 → signs of global units → real signs → big Hilbert quotient → small Hilbert quotient → 1 is exact. The first map is injective, the kernels and images match, and the last map is surjective.
- `bigToSmallHilbertKernelEquivNarrowClassKernel`: the kernel of the transition is isomorphic to the kernel of Cl⁺(K) → Cl(K).
- `realSignModuloIntegralUnitSignsEquivNarrowClassKernel` and `realSignModuloIntegralUnitSignsEquivBigToSmallHilbertKernel`: both kernels are isomorphic to the real sign group modulo the image of the global units (𝓞_K)ˣ.
- `bigToSmallHilbertKernel_card_eq_realSignQuotient_card`: hence the order of the transition kernel equals the order of that sign quotient.

## Proof

The compatibility of the two transition maps is checked on idèle representatives. The exact sequence and the kernel descriptions are then transported from the imported exact sequence for narrow class groups in `RayClass`. That sequence has two inputs: the range of the unit sign map is the kernel of `signToNarrow`, and the range of `signToNarrow` is the kernel of `narrowToClassGroup`. These are transported along the imported Hilbert quotient isomorphisms.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/HilbertClassFieldComparison.lean`: the Lean file is the source byte for byte (SHA-256 `43cad9c5beea7ba2470346351cd916a566c8849e09b6f1434aebb94b2b5a10fe`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
