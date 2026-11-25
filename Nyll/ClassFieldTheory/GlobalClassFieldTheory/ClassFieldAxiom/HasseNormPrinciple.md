# The Hasse norm principle for cyclic extensions

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.HasseNormPrinciple`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves Hasse's norm theorem for a finite cyclic Galois extension L/K of number fields: an element of Kˣ is a norm from Lˣ exactly when it is a norm at every place. The local condition at a place v is membership in the image of the determinant norm of `K_v ⊗[K] L`. The local-global map is a homomorphism `Kˣ / N(Lˣ) → I_K / (local norm condition)`, whose injectivity is the norm principle.

## Main definitions and results

- `allInfinitePlaceLocalNormCondition`, `allPlaceLocalNormCondition`: ideles whose component at every infinite place (at every place) is a determinant norm from `K_v ⊗[K] L`; the finite-place part is imported.
- `relativeIdeleNorm_range_eq_allPlaceLocalNormCondition`: an idele of K is the norm of an idele of L exactly when every component is a local determinant norm.
- `globalFieldNormSubgroup K L` is `N_{L/K}(Lˣ)`; `everywhereLocalFieldNormSubgroup K L` consists of the units of K whose principal idele meets every local condition. The `..._iff` lemmas match them with the predicates `ClassFieldTheory.IsFieldNorm`, `IsNormAtFinitePlace`, `IsNormAtInfinitePlace`, `IsEverywhereLocalNorm`.
- `globalFieldNormSubgroup_le_everywhereLocalFieldNormSubgroup`: global norms are local norms everywhere.
- `ideleClassToPrincipalConnecting_range_eq_ker`: exactness of `H⁻¹(G, C_L) → H⁰(G, P_L) → H⁰(G, I_L)` in Tate cohomology for `1 → P_L → I_L → C_L → 1`, `G = Gal(L/K)`; `ideleClassToFieldUnitsConnecting_range_eq_ker` is the version with `H⁰(G, Lˣ)`, and `fieldUnitsHerbrandH0EquivGlobalNormQuotient` identifies `H⁰(G, Lˣ)` with `Kˣ / N(Lˣ)`.
- `hasseNormDiagonal`, `hasseNormDiagonal_injective_iff`, `..._iff_subgroup_eq`: injectivity is equivalent to the equality of the two subgroups.
- `hasseNormPrinciple_of_subsingleton` (with injectivity and inclusion forms): the norm principle for a finite Galois extension once `H⁻¹(G, C_L)` is trivial.
- `hasseNormPrinciple_cyclic`, `hasseNormDiagonal_injective_cyclic` (with `_native` versions): the theorem when `Gal(L/K)` is cyclic.

## Proof

If x is a local norm everywhere, its principal idele is an idele norm, so its class in `H⁰(G, Lˣ)` dies in `H⁰(G, I_L)`; vanishing of `H⁻¹(G, C_L)` makes that map injective, so x is a norm. In the cyclic case the vanishing is the imported `ideleClass_tateHMinusOne_subsingleton_cyclic`. The universe-polymorphic statement is reduced to `Type` through `Shrink` small models.

## Points to watch

- The general statements take the triviality of `H⁻¹(G, C_L)` as a `Subsingleton` instance hypothesis; only the cyclic case discharges it, so the norm principle is proved for cyclic extensions only.
- The connecting maps from `H⁻¹(G, C_L)`, their exactness theorems, and the `_native` and `_of_subsingleton` statements need K and L in `Type`; `hasseNormPrinciple_cyclic` and `hasseNormDiagonal_injective_cyclic` are universe-polymorphic.
- The field predicates and the infinite-place condition use `K_v ⊗[K] L`, not a chosen completion of L; the finite part of the idelic condition is the library's chosen completion norm subgroup, which an imported lemma identifies with the tensor norm image.
- `H⁰` is the library's `HerbrandH0`, fixed points modulo norms.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/HasseNormPrinciple.lean`: the Lean file is the source byte for byte (SHA-256 `ef8ed4f5ba1ebdd89884619b57ae607c0cdfa5688de1f43178846a20c04cf9c7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
