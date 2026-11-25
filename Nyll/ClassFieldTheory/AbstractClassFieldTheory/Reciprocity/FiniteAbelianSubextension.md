# Finite abelian extensions and their norm subgroups

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the library's abstract class field theory, a field is represented by a closed subgroup of a group `G` with a topology (its "absolute Galois group"). This file sets up the extension side of the classification of finite abelian extensions of `K` by norm subgroups: the extensions themselves, their order, composita, intersections, and the assignment `L ↦ N(A_L)`, the image of the norm from `L` to `K`. It proves only the inclusions that hold without reciprocity.

## Definitions

- `FiniteAbelianSubextension K`: a finite Galois subextension of `K` (`FiniteGaloisSubextension`) whose Galois quotient `G_K / G_L` is commutative. `extensionQuotient` is that quotient, with its `CommGroup` and `Finite` instances. Two such extensions with the same field are equal (`ext`).
- The partial order is field inclusion. Write `H₁`, `H₂` for the closed subgroups representing `L₁`, `L₂`; then `L₁ ≤ L₂` means `H₂ ≤ H₁`.
- `compositum L₁ L₂`: the field with group `H₁ ∩ H₂`. It is the least upper bound (`le_compositum_left`, `le_compositum_right`, `compositum_le`).
- `intersection L₁ L₂`: the field with group `H₁ ⊔ H₂`, which equals the product set `H₁·H₂`. It is the greatest lower bound (`intersection_le_left`, `intersection_le_right`, `le_intersection`).
- `baseChange M L`: for any abstract field `L` containing `K` (`G_L ≤ G_K`), the extension of `L` cut out by the subgroup `G_M ∩ G_L`.
- `normSubgroup A L`: the norm subgroup `N(A_L) ⊆ A_K`.

## Results

- `normSubgroup_antitone`: if `L₁ ≤ L₂` then `N(L₂) ≤ N(L₁)`. The proof uses transitivity of norms in the tower `K ⊆ L₁ ⊆ L₂`.
- `normSubgroup_compositum_le_inf`: `N(L₁L₂) ≤ N(L₁) ∩ N(L₂)`.
- `sup_normSubgroup_le_intersection`: `N(L₁) + N(L₂) ≤ N(L₁ ∩ L₂)`.

## Watch for

- The order is reversed with respect to subgroup inclusion.
- `intersection` needs `G` to be a compact topological group. Compactness is used to show that the product `H₁·H₂` is closed.
- Only one inclusion of each norm formula is proved here. The reverse inclusions, and the classification bijection itself, depend on the reciprocity theorem and are not stated in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`: the Lean file is the source byte for byte (SHA-256 `a16eb9481d44948f789976079e009ddc8691626e6b2d07c1afe346fe28d15171`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
