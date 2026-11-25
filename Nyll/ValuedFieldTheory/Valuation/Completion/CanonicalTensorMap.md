# The canonical map from `K_v ⊗_K L` to the product of the completions

Module `Nyll.ValuedFieldTheory.Valuation.Completion.CanonicalTensorMap`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `v` be a real absolute value on `K`, `K_v` its completion and `L/K` a field extension. For each absolute value `w` on `L` extending `v`, multiplication in the completion `L_w` gives a map `K_v ⊗_K L → L_w`. The file assembles these into the canonical `K_v`-algebra map to the product of all `L_w`.

## Main definitions

- `completionTensorMap_leftCanonicalHom v : K_v ⊗_K L →ₐ[K_v] ∏_w L_w`, with `b ⊗ a ↦ (b · a)_w`, built from the library's component maps `absoluteValueExtension_localizationTensorHom`.
- `completionTensorMap_canonicalHom v`: the same map with the factors in the order `L ⊗_K K_v`, so that `a ⊗ b ↦ (a · b)_w`.

## Points to watch

- The product runs over the type `AbsoluteValueExtension v L` of absolute values on `L` that restrict exactly to `v`, not over equivalence classes of places.
- No finiteness, separability or nontriviality is assumed, and bijectivity is not proved here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Completion/CanonicalTensorMap.lean`: the Lean file is the source byte for byte (SHA-256 `c117e2766d7e7620f9ea0065aa18326645800766b2526b4402a052dca8c05de0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
