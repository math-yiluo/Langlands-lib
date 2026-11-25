# Restriction of local Galois groups across a square of number fields

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.CrossLocalRestriction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Consider number fields K ⊆ K' and L ⊆ L' with K ⊆ L and K' ⊆ L' compatibly (scalar towers K → K' → L' and K → L → L'), L/K finite abelian and L'/K' abelian. Take a finite place v of K, a place W of K' above v, an extension w of v to L and an extension w' of W to L'. The hypothesis `hcentres` asks that the prime of L below the centre of w' be the centre of w. This file builds the maps between the completions in this square. It shows that restricting local automorphisms from E'/K'_W to L_w/K_v, with E' the localized completion of L' at w', agrees, through decomposition groups, with restricting global automorphisms from Gal(L'/K') to Gal(L/K).

## Main definitions

- `finitePlaceArtinRelativeCompletionRingHom v W hW`: the map K_v → K'_W of completions for the absolute values `adicAbv`, defined through Mathlib's adic completions; it is continuous.
- `finitePlaceArtinLocalizedCompletion` and `finitePlaceArtinLocalizedAutomorphism`: abbreviations for the localized completion L_w and its group of K_v-automorphisms, with the algebra structures fixed. `finitePlaceArtinLocalizedCompletionBaseRingHom` is the map K_v → L_w.
- `finitePlaceArtinLocalizedCompletionRingHom v W w w' hcentres`: the map L_w → E'.
- `finitePlaceCrossLocalRestrictionMonoidHom`: Gal(E'/K'_W) →* Gal(L_w/K_v). It restricts scalars to K_v and then restricts to L_w. It commutes with the map L_w → E' (`..._commutes`).

## Main results

- `finitePlaceArtinLocalizedCompletion_towerPoint`: the square K_v → K'_W → E' and K_v → L_w → E' commutes.
- `finitePlaceCrossDecompositionTransport`: for τ ∈ Gal(E'/K'_W), take its image in Gal(L'/K') under `finitePlaceLocalToGlobalMonoidHom`, restrict scalars to K and restrict to L. The result is the image in Gal(L/K) of the local restriction of τ.

## Proof

The completion maps are compared through Mathlib's `adicCompletion`, using `finitePlaceAdicCompletionMap_comp`. The main theorem then follows from an abstract private lemma comparing two restrictions through embeddings compatible with the Galois actions.

## Points to watch

- `hcentres` is a hypothesis: the two chosen places must be compatible. The file does not construct such a pair.
- Despite the module title, no Artin homomorphism appears here. The file covers only the restriction maps and the decomposition-group transport that a compatibility of Artin maps would use.
- Both L/K and L'/K' are assumed abelian. The local restriction uses normality of L_w/K_v, which follows from the abelian hypothesis on L/K; the global restriction uses normality of L/K.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/FinitePlaceArtin/CrossLocalRestriction.lean`: the Lean file is the source byte for byte (SHA-256 `e3511866cb9cbc5f2116d3f7f9742b119e12be6e3840f1230eddd91da3d7ae05`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
