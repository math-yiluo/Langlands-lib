# Images of local tensor norms at infinite places

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.InfinitePlaceTensorNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a Galois extension of number fields and v an infinite place of K. This file shows that the image of the determinant norm (K_v ⊗_K L)ˣ → K_vˣ is the norm group N(L_wˣ) of the completion of L at any infinite place w above v. It is the archimedean counterpart of the corresponding result at finite places.

## Main result

- `infiniteTensorNormSubgroup_eq_localNormSubgroup`: for an infinite place w of L with w restricting to v, `infiniteTensorNormSubgroup v` (the image of the determinant norm on `(v.Completion ⊗[K] L)ˣ`) equals `localNormSubgroup v.Completion w.Completion`, the image of the field norm from L_wˣ to K_vˣ.

## Proof

The proof passes through the completion of K for the absolute value of v, where the imported local result `localTensorNormSubgroup_eq_localNormSubgroup` applies. Mathlib's completions `v.Completion` and `w.Completion` are compared with this model by `infinitePlaceCompletionAlgEquiv`, which turns one determinant norm into the other (`map_norm_tensorProduct_baseChange`). The library's `LocalizedCompletion` of L at w is compared with `w.Completion` through `localizedCompletionEquivCompletion`. Field norms are carried along these compatible ring isomorphisms by `normUnits_map_ringEquiv`.

## Points to watch

- The equality holds for every w above v, not only for a chosen one. The statement assumes L/K Galois.
- `infiniteTensorNormSubgroup` and `localNormSubgroup` are the library's own definitions, from imported files.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Relative/InfinitePlaceTensorNorm.lean`: the Lean file is the source byte for byte (SHA-256 `586d2c2f9554756a480cb775f3a9fd7464b332b4aa9967917ee4a0985a28b02a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
