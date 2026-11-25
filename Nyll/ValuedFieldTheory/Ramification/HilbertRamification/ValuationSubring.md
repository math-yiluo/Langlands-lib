# Decomposition, inertia and ramification groups of a valuation subring

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field extension L/K and a valuation subring A of L, the file sets up the basic Hilbert theory: the decomposition group D, the inertia group I, the ramification group R, their fixed fields, and how they behave under the Galois correspondence and under change of the base field.

## Groups and fields

- `decompositionGroup K A` and `inertiaGroup K A` abbreviate Mathlib's `A.decompositionSubgroup K` and `A.inertiaSubgroup K`. I is a subgroup of D.
- `residueAction K A`: the action of D on the residue field of A by ring automorphisms. Its kernel is I (`residueAction_ker`), so I is normal.
- `automorphismUnitQuotient K A σ x`: the unit σ(x)/x for x in Lˣ, with its cocycle law.
- `ramificationGroup K A`: the elements of I with σ(x)/x a principal unit of A for every x in Lˣ. The library defines this group itself.
- `decompositionField`, `inertiaField`, `ramificationField`: the fixed fields Z, T and V of D, I and R, taken through copies of I and R inside the K-automorphisms of L. The file proves Z ≤ T ≤ V.

## Finite extensions

For L/K finite-dimensional:

- the fixing subgroups of Z, T and V are D, I and R, and each group is isomorphic to the automorphism group of L over its fixed field;
- L/Z is Galois (`decompositionField_isGalois`), and I, transported to Gal(L/Z), is normal with fixed field T;
- `decompositionGroupQuotientInertiaEquivGalInertiaFieldOverDecomposition_of_finiteDimensional`: D/I is isomorphic to the group of Z-automorphisms of T.

## Change of base field

For K ⊆ M ⊆ L, `restrictAutomorphismScalars` views M-automorphisms of L as K-automorphisms. Under this map:

- `decompositionGroup_range_eq_inf`: D over M maps onto D over K intersected with the M-automorphisms;
- `inertiaGroup_range_eq_inf`: I over M maps onto I over K intersected with the image of D over M;
- `ramificationGroup_range_eq_inf`: R over M maps onto R over K intersected with the image of I over M.

## Residue action

- `inertia_subtype_mulExact_residueAction`: I → D → Aut(residue field of A) is exact at D.
- `quotientInertiaEquivResidueActionRange`: D/I is isomorphic to the range of the residue action.
- `galInertiaFieldOverDecompositionEquivResidueActionRange_of_finiteDimensional`: for finite L/K, the Z-automorphisms of T form a group isomorphic to that range.

## Watch for

- The residue action is not shown to be surjective, which the file's comment says can fail for an arbitrary valuation subring. Every comparison uses its range.
- The residue action takes values in all ring automorphisms of the residue field, not in automorphisms over a residue field of K.
- L/K is never assumed Galois. The groups sit inside the K-automorphisms of L, and the correspondence statements assume only finite dimension.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationSubring.lean`: the Lean file is the source byte for byte (SHA-256 `b8d48749565a6181951b79de8369855cc1e387604f5c06750cb5c242fe870931`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
