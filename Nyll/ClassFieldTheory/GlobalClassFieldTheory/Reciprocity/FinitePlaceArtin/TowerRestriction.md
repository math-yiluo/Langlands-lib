# Restriction to an intermediate field for finite-place Artin maps

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.TowerRestriction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite abelian extension of number fields and E an intermediate field (K → E → L a scalar tower) with E/K finite abelian Galois. The file restricts extensions of a finite place v of K from L to E and proves that the finite-place Artin maps commute with restriction Gal(L/K) → Gal(E/K).

## Main definitions and results

- `restrictFinitePlaceExtension v w`: an extension w of the adic absolute value of v to L, composed with E → L, is an extension to E.
- `absoluteValueCompletionMap_comp_of_isScalarTower`: completion maps compose along a tower K → E → L when the three absolute values extend one another.
- `finitePlaceRestrictedLocalizedCompletionAlgHom v wL`: the map, over the completion of K, from the localized completion of E at the restricted place to that of L at wL, built from the completion map; `finitePlaceRestrictedLocalizedCompletionAlgHom_toAlgebraicLocalization` says it extends E → L.
- `decompositionGroupEquivAlgebraicLocalizationAut_restrict_of_commutes`: for a nontrivial absolute value of K and any embedding of localized completions compatible with E → L, restricting a decomposition-group element from L to E matches restricting the corresponding local automorphism. `finitePlaceDecompositionTransport_restrict_tower` and its `_apply` form specialise this to the map above.
- `finitePlaceLocalRestrictionMonoidHom v wL`: restriction of automorphisms of the localized completion of L to that of E.
- `finitePlaceLocalArtinMonoidHom_restrict_tower`: local restriction composed with the local Artin map for L equals the local Artin map for E at the restricted place.
- `finitePlaceArtinMonoidHomOfExtension_restrict_tower`: `AlgEquiv.restrictNormalHom E` composed with `finitePlaceArtinMonoidHomOfExtension v wL` equals `finitePlaceArtinMonoidHomOfExtension` for E at the restricted extension.
- `chosenFinitePlaceArtinMonoidHom_restrict_tower`: restriction to E composed with `chosenFinitePlaceArtinMonoidHom` for L equals `chosenFinitePlaceArtinMonoidHom` for E.

## Proof

The local statement is the local tower compatibility `LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom_restrict_tower`, transported through the identification of units of the absolute-value completion with units of `v.adicCompletion K`. The global statement factors the Artin map through `finitePlaceLocalToGlobalMonoidHom` (`finitePlaceArtinMonoidHomOfExtension_factor`) and uses the decomposition-group transport. The chosen version adds `finitePlaceArtinMonoidHomOfExtension_eq`, which relates the Artin map at the restricted chosen extension to the one at the chosen extension for E.

## Points to watch

- The local fields are the library's `LocalizedCompletion` (an algebraic localization inside the completion), not Mathlib's adic completions; the algebra structure between the two localized completions is installed locally by `letI`, not as an instance.
- The restriction results assume E/K abelian; the map of localized completions needs only `IsGalois K E`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/FinitePlaceArtin/TowerRestriction.lean`: the Lean file is the source byte for byte (SHA-256 `68f6b122fe22a6f979fc7aaa32fda1f2ce020dad14f447f35689ff1b32230d97`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
