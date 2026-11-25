# Norms of units and degree-zero Tate cohomology

Module `Nyll.GaloisCohomology.Cyclic.TateH0.NormImage`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field extension L/K with finite automorphism group, the file studies the norm of the representation of `Gal(L/K)` on `Lˣ` (written additively): it lands in the invariant units, and the invariant units modulo its image are the degree 0 Tate group. For L/K finite Galois the representation norm is the field norm, and under the identification of invariant units with `Kˣ` the norm image becomes the subgroup of field norms.

## Main definitions and results

- `unitsNormLinearMap K L` is the norm `x ↦ ∑σ σ·x` of `Rep.ofAlgebraAutOnUnits K L`; its values are invariant (`unitsNorm_mem_invariants`), and `unitsNormToInvariantsLinearMap` is the map into `unitsInvariantSubmodule K L`.
- `unitsTateH0NormSubmodule K L` is the image of that map.
- `tateUnitsH0IsoInvariantsQuotient`: for K, L in `Type`, Mathlib's `tateCohomology` of the unit representation in degree 0 is isomorphic to the invariant units modulo `unitsTateH0NormSubmodule`.
- `integralTateUnitsH0AddEquivInvariantsQuotient` and `universeTateUnitsH0AddEquivInvariantsQuotient`: the same quotient for `IntegralGroupCohomology.tate` and `IntegralGroupCohomology.Universe.tate`, in any universes; `integralUnitsTateClass K L x` is the Tate class of an invariant unit x, with its compatibility lemmas `integralTateUnitsH0AddEquivInvariantsQuotient_class` and (in universe 0) `integralUnitsTateClass_original`.
- `unitsNormLinearMap_apply_val`: for L/K finite Galois, the representation norm of a unit x is `Algebra.norm K x`, viewed in L.
- `additiveNormSubgroup K L` is the library's norm subgroup `localNormSubgroup K L` of `Kˣ` written additively; it is the kernel of the norm-class map (`additiveNormSubgroup_eq_ker_quotient_map`).
- `invariantsUnitsAddEquivBaseUnits_unitsNorm_apply`: the isomorphism of invariant units with `Kˣ` sends the norm of x to `normUnits K L x`. `invariantsUnitsAddEquivBaseUnits_map_tateNormSubgroup` and `invariantsUnitsEquivBaseUnits_map_tateNormSubmodule`: it maps `unitsTateH0NormSubmodule` onto `additiveNormSubgroup`.
- `invariantsUnitsAddEquivBaseUnits_unitsNorm_tower`: in a tower K ⊆ M ⊆ L with L finite Galois over K and over M, taking the norm to M and then the norm to K agrees with taking the norm to K (using `normUnits_tower`).

## Proof

The Tate isomorphisms start from `TateCohomology.isoZeroBoundary`: the kernel of the first cochain differential is the invariants and the boundaries are the norm image. The norm formula is Mathlib's `Algebra.norm_eq_prod_automorphisms`.

## Watch for

- The comparison with Mathlib's Tate cohomology (`tateUnitsH0IsoInvariantsQuotient`) is stated only for K and L in universe 0.
- Units are written additively (`Additive Lˣ`, `Additive Kˣ`), so the norm is a sum.
- `localNormSubgroup`, `normUnits` and `normClass` are the library's own definitions, imported through its norm-quotient file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/TateH0/NormImage.lean`: the Lean file is the source byte for byte (SHA-256 `d9aada12898fdaf365343a72852000cedf173104a6064796118f6b3523cd2ea6`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
