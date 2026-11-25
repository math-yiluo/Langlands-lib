# Norm subgroups of finite abelian extensions as an order embedding

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library describes finite abelian extensions of a field `K` abstractly, as objects of `FiniteAbelianSubextension (intrinsicAbstractBase K)` built from closed subgroups of `Gal(SeparableClosure K / K)`. This file sends each such object to the ordinary norm subgroup `N(Eˣ) ⊆ Kˣ` of its fixed field `E`, and shows, for a nonarchimedean local field `K`, that this is an order embedding into the opposite poset of open finite-index subgroups of `Kˣ`.

## Main definitions and results

For any field `K`:

- `finiteAbelianSubextension_finite_over_absoluteBase`, `finiteAbelianSubextension_normal_over_absoluteBase`: finite index and normality pass from the ground-field fixing group to the abstract `baseField`.
- `finiteAbelianNormSubgroup K L`: the norm subgroup `localNormSubgroup K E` of the fixed field `E` of `L`.
- `finiteAbelianSubextension_fixedField_isAbelianGalois`: `E` is abelian Galois over `K`; commutativity is transported along an isomorphism of the abstract extension quotient with `Gal(E / K)`.
- `finiteAbelianSubextension_compositum_fixedField`: the fixed field of the abstract compositum is the compositum of the fixed fields.
- `relativeNorm_abstractFixedFieldUnit_val_of_isGalois` and `baseUnitsEquivGaloisAmbientFixed_symm_relativeNorm_abstractFixedFieldUnit_eq_normUnits`: for a closed subgroup `H` of finite index whose fixed field is finite Galois over `K`, the class-formation relative norm of a unit is its field norm.
- `map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup`: transported to `Kˣ`, the abstract norm subgroup equals the ordinary one (in additive notation); `finiteAbelianNormSubgroup_le_of_abstractNormSubgroup_le_map` transports containments.

For `[IsNonarchimedeanLocalField K]`:

- `finiteAbelianNormSubgroup_isOpen`, `finiteAbelianNormSubgroup_finiteIndex`: the norm subgroup is open and of finite index; finiteness comes from `abelianizationEquivNormQuotient`, which identifies `Kˣ / N(Eˣ)` with the abelianization of the finite group `Gal(E / K)`.
- `finiteAbelianNormSubgroupMap` with `finiteAbelianNormSubgroupMap_injective`: the map into `OpenFiniteIndexSubgroup K`, and its injectivity.
- `finiteAbelianSubextension_le_iff_normSubgroup_le`: `L₁ ≤ L₂` if and only if `N(L₂) ≤ N(L₁)`.
- `finiteAbelianNormSubgroupOrderEmbedding`: the order embedding into `(OpenFiniteIndexSubgroup K)ᵒᵈ`.

## Proof

Injectivity and order reversal are transported from the abstract class-formation statements `FiniteAbelianSubextension.normSubgroupMap_injective` and `FiniteAbelianSubextension.le_iff_normSubgroup_le`, applied to `localHenselianValuation K` and `separableClosureUnits_isClassFormation K`, through the identification of abstract and ordinary norm subgroups.

## Points to watch

- This is one half of the existence theorem: surjectivity, that every open subgroup of finite index is a norm subgroup, is not proved here.
- The order on `FiniteAbelianSubextension` is the library's own order on abstract subextensions, not Mathlib's order on intermediate fields.
- Only the results through `finiteAbelianSubextension_compositum_fixedField` allow `K` in any universe; everything from `relativeNorm_abstractFixedFieldUnit_val_of_isGalois` on, including the local results, takes `K : Type` in universe `0`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`: the Lean file is the source byte for byte (SHA-256 `2617f3e68c4d7f6b038c0cb5822e83e2081dcb0de9252b448f79bbd77292b555`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
