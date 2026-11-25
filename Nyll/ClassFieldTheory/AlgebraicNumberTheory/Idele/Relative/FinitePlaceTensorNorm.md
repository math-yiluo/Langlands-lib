# Images of local tensor norms at finite places

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension of number fields and v a finite place of K. This file identifies the image of the determinant norm (K_v ⊗_K L)ˣ → K_vˣ with the norm group N(L_wˣ) of one chosen completion L_w. It does so by comparing the completion of K for the v-adic absolute value with Mathlib's adic completion K_v. As a consequence, the finite components of global relative-idele norms are local norms.

## Main definitions and results

- `finitePlaceCompletionAlgEquiv v`: the comparison between the two completions, as a K-algebra isomorphism. `finitePlaceLocalTensorAlgEquiv` and `finitePlaceLocalTensorUnitsEquiv` are the induced isomorphisms of the tensor algebras with L and of their unit groups.
- `finitePlaceLocalTensorNorm_commutes`: these isomorphisms carry one determinant norm to the other.
- `finitePlaceLocalTensorNorm_range_eq_transport`: the range of `localTensorNorm` at v is the transport of `localTensorNormSubgroup` from the absolute-value model. No Galois hypothesis is needed here.
- `finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup`: the range of the determinant norm on K_v ⊗_K L equals `chosenFinitePlaceLocalNormSubgroup v`, the norm group of the completion L_w for the extension w chosen at v. It rests on the imported local result `localTensorNormSubgroup_eq_localNormSubgroup`.
- `finitePlaceTensorNormClass v`: the projection of K_vˣ onto the quotient by that subgroup. By `finitePlaceTensorNormClass_eq_one_iff` and `finitePlaceTensorNormClass_ker`, the class of x is trivial exactly when x is a determinant norm from K_v ⊗_K L.
- `relativeIdeleNorm_finiteComponent_mem_chosenLocalNormSubgroup` and `finitePlaceTensorNormClass_relativeIdeleNorm`: for every relative idele a, the v-component of its norm lies in the chosen subgroup, and its class is trivial.

## Points to watch

- The identification with the norm group of a single L_w uses that L/K is Galois. `chosenFinitePlaceLocalNormSubgroup` is defined through one extension w, chosen noncanonically.
- `localTensorNorm`, `RelativeIdeleGroup` and the chosen subgroups are the library's own constructions, from imported files.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Relative/FinitePlaceTensorNorm.lean`: the Lean file is the source byte for byte (SHA-256 `a7e7c6f4713c557104594c0842efb8f7ad408961413e2045f882bfade8cd1790`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
