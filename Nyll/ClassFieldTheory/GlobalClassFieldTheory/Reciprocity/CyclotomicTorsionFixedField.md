# The cyclotomic torsion fixed field and its ℤ̂ coordinate

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicTorsionFixedField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library's `rationalCyclotomicField` is ℚ(μ∞) inside `SeparableClosure ℚ`, and the cyclotomic character identifies its Galois group with ℤ̂ˣ. The file takes the fixed field of the torsion closure of this group (`rationalCyclotomicTorsionFixedField`, defined elsewhere) and shows that its Galois group over ℚ is ℤ̂, as a topological group. This is the Galois group of the cyclotomic ℤ̂-extension.

## Main definitions and results

- `rationalCyclotomicTorsionRestrictionEquiv`: restriction identifies the quotient of Gal(ℚ(μ∞)/ℚ) by the torsion closure with the Galois group of the torsion fixed field, as a continuous multiplicative isomorphism.
- `rationalCyclotomicTorsionFixedFieldGalEquivZHat`: the Galois group of the torsion fixed field is isomorphic to `Multiplicative ZHat`, as topological groups.
- `rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal` (simp): an automorphism σ of ℚ(μ∞), restricted to the torsion fixed field, goes to the torsion-free component of its cyclotomic character under `zHatUnitsDecomposition`.

## Proofs

The first isomorphism comes from the infinite Galois correspondence (`InfiniteGalois.normalAutEquivQuotient`). It is a homeomorphism because it is a continuous bijection from a compact group to a Hausdorff group. The second composes its inverse with `torsionQuotientEquivOfZHatMulDecomposition`, applied to the cyclotomic character followed by the decomposition of ℤ̂ˣ, with the density of torsion in the finite part (`dense_torsion_cyclotomicFinitePart`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/CyclotomicTorsionFixedField.lean`: the Lean file is the source byte for byte (SHA-256 `ccccd9f80637f0afe4a0eaf512ff39da8cd0be05ec33387f3fd6a640644264ae`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
