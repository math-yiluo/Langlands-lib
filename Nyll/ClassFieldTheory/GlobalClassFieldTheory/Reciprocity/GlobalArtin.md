# The global Artin homomorphism on ideles

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtin`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite abelian extension L/K of number fields, the file defines the global Artin map I_K → Gal(L/K) on the idele group as the product of the local Artin maps at all places, and proves that it kills idele norms, is compatible with norm and restriction, and is surjective.

## Main definitions and results

- `globalArtinMonoidHom`: the product of `infinitePlaceGlobalArtinMonoidHom` and `finitePlaceGlobalArtinMonoidHom`; it is continuous (`globalArtinMonoidHom_continuous`). By `globalArtinMonoidHom_apply`, its value at a is the product over infinite places v of `chosenInfinitePlaceArtinMonoidHom v` of the v-component, times the finite product (`finprod`) over finite places of `chosenFinitePlaceArtinMonoidHom v` of the v-component.
- `globalArtinMonoidHom_relativeIdeleNorm_eq_one` and `globalArtinMonoidHom_ideleNorm_eq_one` (simp): the map is trivial on norms from I_L, for the relative idele norm and for `IdeleGroup.norm K L`. This is checked place by place with the local kernel theorems (`chosenFinitePlaceArtinMonoidHom_ker`, `chosenInfinitePlaceArtinMonoidHom_ker`).
- `globalArtinMonoidHom_norm_eq_place_products`: for a number field M over K and a ∈ I_M, the Artin symbol of `IdeleGroup.norm K M a` is the product over the places W of M of the local Artin symbol, at the place below W, of the local norm of the W-component.
- `globalArtinMonoidHom_norm_restriction`: for number fields K ⊆ K', L ⊆ L' in scalar towers with L'/K' abelian, restriction Gal(L'/K') → Gal(L/K) composed with the Artin map of L'/K' equals the Artin map of L/K composed with `IdeleGroup.norm K K'`. `restrict_globalArtinMonoidHom_apply` distributes the restriction over the local factors.
- `globalArtinMonoidHom_restrict_tower`: for an intermediate field E abelian over K, restriction to E composed with the Artin map of L/K is the Artin map of E/K.
- `globalArtinMonoidHom_infinitePlaceIdele`, `globalArtinMonoidHom_finitePlaceIdele` (simp): on an idele supported at one place, the global symbol is the local symbol there. Hence each finite-place decomposition group lies in the image (`finitePlaceDecompositionGroup_le_globalArtinMonoidHom_range`).
- `globalArtinMonoidHom_surjective`: the map is surjective, for K and L in arbitrary universes.

## Proof of surjectivity

Let H be the image and E its fixed field. Every decomposition group lies in H, so every finite place of K splits completely in E; the imported theorem `Cohomology.finrank_eq_one_of_finite_nonSplittingPlaces` (an extension in which all but finitely many finite places split completely is trivial) gives [E : K] = 1, so H is the whole group. This is proved first for fields in `Type` (a private lemma) and then transferred to other universes through `Shrink` models and the norm–restriction square.

## Points to watch

- The file calls this map "preliminary": it is defined on I_K, and nothing here concerns principal ideles or the idele class group.
- The local factors are taken at chosen extensions of each place (`chosenFinitePlaceArtinMonoidHom`, `chosenInfinitePlaceArtinMonoidHom`).
- In `globalArtinMonoidHom_norm_eq_place_products` the algebra structures between completions are installed by `let`, not as instances.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/GlobalArtin.lean`: the Lean file is the source byte for byte (SHA-256 `997e88f8ebc596b09db4c39443e9916da4dd41c09909ab94c6d7f5fbaff13459`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
