# The Artin image of the integral units is the inertia group

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseInertia`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file identifies the image of the unit group 𝒪_K^× under the universe-polymorphic abelian Artin map with the inertia subgroup of Gal(L/K), for fields in arbitrary universes.

## Main result

`abelianLocalArtinMonoidHom_units_eq_residue_ker`: let K : Type u and L : Type v be nonarchimedean local fields (each with `ValuativeRel`, a topology and `IsNonarchimedeanLocalField`), L/K finite abelian Galois, the valuation of L extending that of K, and 𝒪_L the integral closure of 𝒪_K in L (`IsIntegralClosure 𝒪[L] 𝒪[K] L`). Then the image of `fieldPrincipalUnits K 0` (the units of 𝒪_K, as depth-zero principal units) under `abelianLocalArtinMonoidHom K L` is the kernel of `galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L`, the map from Gal(L/K) to automorphisms of the residue field extension.

## Proof

Everything is moved to the small copies `Shrink.{0} K` and `Shrink.{0} L`. There the result is the depth-zero case of native filtered reciprocity, `finiteAbelian_filteredLocalReciprocity`, combined with `localUpperRamificationGroup_zero_eq_residue_ker` (the upper ramification group of index 0 is the residue-action kernel). The two residue-action kernels are matched by the criterion that σ lies in the kernel if and only if σ(a) − a lies in the maximal ideal for every integer a, and the unit groups by `shrinkIntegerUnitsToFieldUnits`.

## Caveats

The inertia group appears only as the kernel of the residue action map, not as a separately defined subgroup. Unlike the Artin map itself, the statement needs a local-field structure on L, a valuation extension and the integral-closure hypothesis.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UniverseInertia.lean`: the Lean file is the source byte for byte (SHA-256 `71cdfd3c7bb4e1f9f2d911cf6b402cabb54aeb7dccd70462135f21a2882fe4db`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
