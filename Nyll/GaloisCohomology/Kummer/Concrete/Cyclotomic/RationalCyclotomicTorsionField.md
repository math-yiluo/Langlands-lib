# The torsion fixed field in ℚ(μ∞)

Module `Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicTorsionField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the Galois group `Gal(ℚ(μ∞)/ℚ)` with its Krull topology, the file takes the closure of the torsion subgroup and its fixed field.

- `rationalCyclotomicTorsionClosure`: the closure of the subgroup of finite-order automorphisms, as a closed subgroup.
- `rationalCyclotomicTorsionFixedField`: the subfield of `ℚ(μ∞)` fixed by it.
- Instances: this fixed field is integral, normal, Galois and abelian Galois over `ℚ`. Normality comes from the closed subgroup being normal in the abelian Galois group; abelianness descends from `ℚ(μ∞)/ℚ`.

The Galois group is Mathlib's automorphism group of `ℚ(μ∞)` over `ℚ`, not `ℤ̂ˣ`; the comparison with `ℤ̂ˣ` is made in other files.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/RationalCyclotomicTorsionField.lean`: the Lean file is the source byte for byte (SHA-256 `35e7ac39302f7a2b4be3cee159efe9c198a6c46bec9e3e1d49f6db1354f48be0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
