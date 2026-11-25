# The narrow finite conductor of an idèle-class subgroup

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.Conductor`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field K and a subgroup H of the idèle class group C_K, a modulus m is called defining when its ray congruence subgroup C_K^m lies in H, that is, when the ray class field of m contains the class field of H. This file constructs the finite part of the conductor of H as the gcd of the finite parts of all defining moduli, rather than postulating it.

## Main definitions and results

- `IsDefiningModulus H m`: the proposition `m.congruenceSubgroup ≤ H`, for a modulus `m : RayClass.Modulus K`.
- `ConductorialSubgroup K`: the subtype of subgroups H that admit at least one defining modulus.
- `ConductorialSubgroup.narrowFiniteConductorExponent H v`: at a finite prime v, the least exponent of v among the finite parts of defining moduli (via `Nat.find`); `narrowFiniteConductorExponent_spec` says it is attained by a defining modulus.
- `ConductorialSubgroup.narrowFiniteConductor H`: the finite modulus with these exponents. Its support is cut out of the finite part of one chosen defining modulus, which bounds it.
- `narrowFiniteConductor_le`, `le_narrowFiniteConductor_iff` and `narrowFiniteConductor_is_gcd`: the conductor divides the finite part of every defining modulus, and any finite modulus dividing all of them divides the conductor.
- `ConductorialSubgroup.isOpen`, `isClosed` and the instance `finiteIndex`: a conductorial subgroup is open, closed and of finite index, since it contains a ray congruence subgroup.
- `exists_definingModulus_of_isClosed_finiteIndex` and `ConductorialSubgroup.ofClosedFiniteIndex`: every closed subgroup of finite index has a defining modulus (through `RayClass.modulusInsideClosedFiniteIndex`), hence gives a conductorial subgroup.

## Points to watch

- The conductor here is only the finite part, in the convention where every real place carries the positivity condition (the "narrow" convention of the file). It is not the full conductor with an archimedean component.
- The minimum is taken over moduli `RayClass.Modulus K` of the library's ray class theory, compared only through their finite parts.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/Conductor.lean`: the Lean file is the source byte for byte (SHA-256 `23174b4cac7fce3cda3b74fccd59c93d4988c4de0ebac061eb78fa8f74178244`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
