# Local-global compatibility of Artin maps at infinite places

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteLocalGlobalArtinCompatibility`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite abelian extension of number fields and v an infinite place of K. This file proves that the global norm-residue map C_K → Gal(L/K), restricted to the idele classes supported at v, is the local Artin map at v. It also identifies which such classes are norms from C_L.

## Main results

- `globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass`: `globalNormResidueMonoidHom K L` composed with `IdeleGroup.infinitePlaceIdeleClass v` (K_v^× → C_K) equals `chosenInfinitePlaceArtinMonoidHom v`. The latter is the library's local Artin map at a chosen place of L above v.
- `infinitePlaceIdeleClass_mem_ideleClassNorm_range_iff` (simp): the class of x ∈ K_v^× lies in the range of the idele class norm C_L → C_K exactly when x lies in `infiniteTensorNormSubgroup v`, the local norm subgroup at v.
- `chosenInfinitePlaceArtinMonoidHom_eq_one_iff_infiniteTensorNorm` (simp): the local Artin symbol of x is trivial exactly when x is a local norm.
- One direction: `infinitePlaceIdeleClass_mem_ideleClassNorm_range_of_mem_infiniteTensorNorm` states that local norms give global idele-class norms. It needs no abelian hypothesis.
- At a real place, positive elements are global norms and have trivial norm-residue symbol (`..._of_real_pos`).
- At a ramified real place, −1 is not a local norm and its local Artin symbol is nontrivial (`neg_one_not_mem_infiniteTensorNormSubgroup_of_ramified`, `chosenInfinitePlaceArtinMonoidHom_neg_one_ne_one_of_ramified`).
- Reductions: the compatibility square commutes at unramified and at complex places. At a real place it is equivalent to its value at −1 (`..._eq_iff_neg_one`, `..._eq_iff_real_neg_one`).

## Proofs

A local norm at v is the norm of a relative idele supported at v. Moving it to an idele of L gives a global norm. At an unramified place both maps are trivial, because the local Artin map is defined to be trivial there. At a real place every unit is, up to the factor −1, positive, and positive units are killed by both maps. That leaves the value at −1 at a ramified real place. This value comes from the imported result `globalNormResidueMonoidHom_infinitePlaceIdeleClass_neg_one_of_ramified`, proved in the complexification files.

## Points to watch

- The local Artin map uses one chosen place of L above v (`chosenInfinitePlaceAbove`). "Ramified" and "unramified" refer to that place.
- `globalNormResidueMonoidHom` and its kernel description (`globalNormResidueMonoidHom_eq_one_iff`) come from an imported file. The file uses that kernel description to turn statements about the symbol into statements about the norm range.
- The main theorem rests on the imported value of the global symbol of −1 at a ramified real place. The present file proves the reduction to that value and applies the imported result; it does not prove the value itself.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/InfiniteLocalGlobalArtinCompatibility.lean`: the Lean file is the source byte for byte (SHA-256 `263f65f38bca9751757a0bc752a4206367327e643752f2e6474fb0c65baee9f9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
