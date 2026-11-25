# Local components of the idele norm

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNormComponents`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For number fields `K ⊆ L`, the idele norm `N : I_L → I_K` (`IdeleGroup.norm`) is defined by transporting the determinant norm of the relative model `𝔸_K ⊗_K L`. The file proves the local formula: the component of `N(a)` at a place `v` of `K` is the product, over the places `W` of `L` above `v`, of the local field norms of the components `a_W`. This holds at finite and at infinite places.

## Main results

- `IdeleGroup.finiteComponent_norm_eq_prod`: for a finite place `v` and `a ∈ I_L`, `(N a)_v = ∏_W normUnits (K_v) (L_W) (a_W)`. The product runs over the finite places `W` of `L` with `finitePlaceBelow W = v`, and `L_W` is a `K_v`-algebra through `finitePlaceAdicCompletionMap`.
- `IdeleGroup.infiniteComponent_norm_eq_prod`: the same for an infinite place `v`, over the infinite places `W` of `L` above `v`, with `normUnits v.Completion W.Completion`.

The other theorems of the file are private steps toward these two.

## Proof

Pull `a` back to a relative idele and take its local component in `K_v ⊗_K L`. Move it to the completion of `K` at the absolute value of `v` (`map_norm_tensorProduct_baseChange`), where the decomposition of `K_v ⊗_K L` into the completions of `L` over `v` turns the determinant norm into a product of local norms (`RelativeIdeleGroup.localNorm_units_eq_prod`). Finally reindex the factors by the places above `v` and move each norm back to the concrete completions (`LocalClassFieldTheory.normUnits_map_ringEquiv`).

## Points to watch

- `LocalFieldTheory.normUnits` is the library's norm map on unit groups of completions.
- Both statements are made under `let`-bound data: a `Fintype` structure on the places above `v`, obtained from their bijection with the extensions `AbsoluteValueExtension` of the absolute value of `v`, and the algebra or `LiesOver` structures linking the completions. The statements hold for these choices.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/IdeleNormComponents.lean`: the Lean file is the source byte for byte (SHA-256 `336eb128b1e1169712d7a9e111f567d5d7e944b1b930a9bc5f7848b2bfcbd498`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
