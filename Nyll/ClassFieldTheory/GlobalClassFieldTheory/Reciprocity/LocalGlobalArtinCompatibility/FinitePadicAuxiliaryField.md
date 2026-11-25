# The auxiliary fixed field for finite-place local-global compatibility

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicAuxiliaryField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite abelian extension of number fields, embedded in ℚ̄ = `SeparableClosure ℚ` by the library's chosen embeddings. Let H and T be the subgroups of Gal(ℚ̄/ℚ) fixing K and L, so Gal(L/K) ≅ H/T. Fix a finite place v of K and a prime p. For a lift τ ∈ H, this file builds the auxiliary field F, the fixed field of the closed subgroup `numberFieldTowerFinitePadicCyclicFixedSubgroup p τ`, and a compositum E ⊇ L over F. It proves the field identities the auxiliary-field argument needs and produces local representatives with equal local and global Artin symbols.

## Main results

- `numberFieldTowerFinitePadicCyclicFixedField p τ`: the field F, an intermediate field of ℚ̄/ℚ. It is finite over ℚ when the p-adic cyclotomic degree of τ is not 1. It contains the copy of K, and F/K is Galois (`numberFieldTowerFinitePadicAuxiliaryBase_isGalois`).
- `numberFieldTowerFinitePadicAuxiliaryAutomorphism p τ` ∈ Gal(E/F): it acts on E ⊆ ℚ̄ as τ and restricts on L to the image of τ in Gal(L/K).
- `numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension`, `...TopPlaceExtension`: the restrictions to F and E of the chosen place of ℚ̄ above v.
- `numberFieldTowerFinitePadicAuxiliaryLocalGlobalRepresentative` gives z ∈ K_v^× whose local Artin symbol and global norm-residue symbol both equal the image of τ in Gal(L/K). Its hypotheses: τ lies in the decomposition group of the chosen place of ℚ̄, its p-adic cyclotomic degree is a positive integer n, and its image in Gal(L/K) is p-primary.
- `exists_numberFieldTowerFinitePadicLift_of_finitePlace`: every element of the decomposition group at v has such a lift τ, with degree a positive integer.
- If the image of τ generates Gal(L/K), then the fixing subgroups of F and L generate H, so F ∩ L = K (`numberFieldTowerFinitePadicCyclicFixedField_inf_topField`). If the image is p-primary and the p-adic cyclotomic degree is a positive integer, then L ⊆ F · `rationalCyclotomicPadicField p` (the library's p-primary cyclotomic field inside its ZHat-extension of ℚ).
- `exists_finitePlaceCyclotomicAuxiliaryFixedField` and `exists_finitePlacePrimaryCyclotomicAuxiliaryFixedField` collect these for a decomposition element generating Gal(L/K).

## Proofs

For the representative: the automorphism lies in the decomposition group of the place of E, so it is the local Artin symbol of some y ∈ F_V^×. E/F is unramified for `rationalCyclotomicDegreeData`, so the imported theorem `globalNormResidueMonoidHomOfEmbedding_comp_finitePlaceIdeleClass_of_abstractFixedFieldUnramified` gives y the same global symbol. The local norm of y to K_v carries both down, by norm-restriction compatibility.

## Points to watch

- "Unramified" for E/F is the notion of the library's abstract class formation attached to `rationalCyclotomicDegreeData`.
- F and E are the library's abstract fixed fields; the file declares global instances `Algebra K F` and `Algebra L E` from the chosen embeddings.
- The representative is an `opaque` definition: only its stated properties are available.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/LocalGlobalArtinCompatibility/FinitePadicAuxiliaryField.lean`: the Lean file is the source byte for byte (SHA-256 `e27a134a8333b50cd43391a32a17d2fd2c52df0b9defeaa238c174685fe121a8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
