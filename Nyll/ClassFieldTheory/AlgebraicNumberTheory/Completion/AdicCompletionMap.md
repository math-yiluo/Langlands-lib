# The canonical map between adic completions

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionMap`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be an extension of number fields, w a finite place of K, and W a finite place of L above w, that is, with `finitePlaceBelow W = w`. The embedding K → L is uniformly continuous for the w-adic and W-adic valuations. This file completes it to a ring homomorphism K_w → L_W between Mathlib's adic completions and records its basic properties.

## Definitions and results

- `finitePlaceAdicCompletionMap K L w W`: the ring homomorphism `w.adicCompletion K → W.adicCompletion L`. It is the completion of the algebra map between the valued copies of K and L, conjugated by Mathlib's identifications `adicCompletion.equiv`.
- `finitePlaceAdicCompletionMap_coe`: on the image of K it is the embedding K → L.
- `finitePlaceAdicCompletionMap_isScalarTower`: with the algebra structure it defines, K → K_w → L_W is a scalar tower.
- `finitePlaceAdicCompletionMap_continuous`: the map is continuous.
- `finitePlaceAdicCompletionMap_self_apply` (simp): for L = K and W = w the map is the identity.
- `finitePlaceAdicCompletionMap_comp`: for a tower K ⊆ M ⊆ L of number fields and finite places v_K, v_M, v_L lying over one another, the map from the completion of K at v_K to that of L at v_L is the composite of the maps through the completion of M at v_M.

## Proofs

The identity and tower statements are proved by density. Both sides are continuous and agree on the image of K by the formula on K, so they agree everywhere.

## Points to watch

- A place above w is given as a subtype element: a finite place W of L together with a proof that `finitePlaceBelow W = w`. The function `finitePlaceBelow`, which sends a finite place of L to the place of K below it, is the library's own.
- `finitePlaceAdicCompletionMap_comp` takes three separate hypotheses: `hMK` and `hLM` for the successive restrictions, and `hLK` for the restriction of v_L directly to K. It does not derive the third from the first two.
- No finiteness of L/K is assumed in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Completion/AdicCompletionMap.lean`: the Lean file is the source byte for byte (SHA-256 `f4bbdbc5b98fd2064046fc8a052dac140ff09656b765dcc1094fccf1c494c1ac`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
