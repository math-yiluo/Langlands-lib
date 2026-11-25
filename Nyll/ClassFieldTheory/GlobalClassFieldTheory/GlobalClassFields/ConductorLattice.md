# Narrow finite conductors of intersections and joins

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorLattice`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For subgroups of the idèle class group C_K of a number field K that admit a defining modulus (the library's `ConductorialSubgroup K`), this file computes the narrow finite conductor of an intersection and bounds that of a join. A larger modulus has a smaller ray congruence subgroup. As a result, the narrow finite conductor of H ∩ J is the pointwise maximum (lcm) of the conductors of H and J. Under the class field correspondence this is the finite part of the conductor of a compositum.

## Main definitions and results

- `rayClassCongruenceSubgroup_antitone` (with finite, infinite and idèle variants): if m ≤ n then C_K^n ≤ C_K^m. `isDefiningModulus_mono` follows: a modulus larger than a defining one is defining.
- `ConductorialSubgroup.narrowFiniteConductor_isDefiningModulus`: the narrow finite conductor, made into a modulus with positivity at every real place (`RayClass.Modulus.narrowOfFinite`), is a defining modulus.
- `ConductorialSubgroup.inf` and `ConductorialSubgroup.sup`: the conductorial subgroups H ∩ J and H ⊔ J.
- `narrowFiniteConductor_inf`: the narrow finite conductor of H ∩ J equals the join of those of H and J. Hence (`narrowFiniteConductor_inf_support`) its support is the union of the two supports.
- `narrowFiniteConductor_sup_le_inf`: the narrow finite conductor of H ⊔ J divides the pointwise minimum of the two conductors.

## Proof

The equality for intersections combines the minimality of the conductor among defining moduli with the imported antitonicity `narrowFiniteConductor_antitone` (a larger subgroup has a smaller conductor). It also uses the imported existence of a defining modulus whose finite part is exactly the narrow finite conductor.

## Points to watch

- For joins only one divisibility is proved, not an equality with the pointwise minimum.
- These are statements about finite parts in the narrow convention; the archimedean part of the conductor is not treated here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ConductorLattice.lean`: the Lean file is the source byte for byte (SHA-256 `64b9b9e1415bb30221a015a5239263b352d3d3b3b691ea1954450575f2255d8f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
