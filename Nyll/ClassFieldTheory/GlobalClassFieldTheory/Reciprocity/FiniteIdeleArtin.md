# The product of local Artin maps over the finite places

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteIdeleArtin`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite abelian extension of number fields. For an idele a of K, the local Artin symbols of its finite components are trivial at all but finitely many finite places. This file takes their product directly in Gal(L/K), which gives a continuous homomorphism from the idele group of K. It then proves the norm–restriction compatibility of this product.

## Main definitions and results

- `finitePlaceArtinFactors_hasFiniteMulSupport`: for each idele a, the map v ↦ `chosenFinitePlaceArtinMonoidHom v (finiteComponent v a)` has finite support. The supporting lemma `chosenFinitePlaceArtinMonoidHom_eq_one_of_integral_of_unramifiedAt` says that the local Artin map kills a unit component at a place v where the chosen prime of L above v is unramified.
- `finitePlaceGlobalArtinMonoidHom : IdeleGroup K →* Gal(L/K)`: a ↦ ∏ᶠ over finite places v of the local Artin symbol of a_v.
- `finitePlaceGlobalArtinMonoidHom_continuous`: it is continuous for the idele topology and the (discrete) Krull topology.
- `finitePlaceGlobalArtinMonoidHom_finitePlaceIdele` (simp): on an idele supported at one finite place v, the product is the local symbol at v.
- `finitePlaceGlobalArtinMonoidHom_norm_eq_finprod_fibers` and `..._norm_eq_finprod`: for any number field M over K and an idele a of M, the product evaluated at the idele norm of a from M to K equals the product, over the finite places W of M, of the local symbol at the place below of the local norm of a_W. `normUnits_mem_finitePlaceIntegerUnits` (local norms of integral units are integral units) and a finite-support lemma for these factors support this.
- `finitePlaceGlobalArtinMonoidHom_norm_restriction`: for abelian extensions L/K and L'/K' with K ⊆ K', L ⊆ L' compatibly, restricting the product for L'/K' to Gal(L/K) equals the product for L/K composed with the idele norm from K' to K.

## Proofs

Finite support uses that ideles are integral almost everywhere and that only finitely many primes ramify (`finite_ramified_base_heightOne_primes`), together with the kernel of the local Artin map being the local norm group, which contains the integral units at unramified places. Continuity: the product is trivial on the open set of ideles that are local units outside the ramified places and in the local norm group at them. The norm–restriction identity reorganizes the product over fibres (`finprod_fibers_eq_sigma`) and applies the local identity `chosenFinitePlaceArtinMonoidHom_norm_restriction`.

## Points to watch

- Only finite places enter. Archimedean components of the idele are ignored, so this is not the full global Artin map. The file does not show that it is trivial on principal ideles.
- The local maps are the library's chosen local Artin homomorphisms, defined through a chosen place of L above each v.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/FiniteIdeleArtin.lean`: the Lean file is the source byte for byte (SHA-256 `dea3b2c0b72119fde79d8e7b7fa01b02147c4b6a8614ef8849d4ecdc9c1ccb25`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
