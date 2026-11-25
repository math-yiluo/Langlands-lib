# Norms of ideles supported at one finite place

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.OnePlaceBaseNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K ⊆ L` be number fields, `W` a finite place of `L`, and `v` the place of `K` below it. The file computes the idele norm of an idele of `L` that is a unit `y ∈ L_Wˣ` at `W` and `1` elsewhere: it is the idele of `K` that is the local norm of `y` at `v` and `1` elsewhere. The same holds for idele classes.

## Main declarations

- `finitePlaceBaseUnitExtension W : K_vˣ →* L_Wˣ`, induced by the completion map `finitePlaceAdicCompletionMap`.
- `finitePlaceCompletionDegree W`: the degree `[L_W : K_v]`, which is positive (`finitePlaceCompletionDegree_pos`).
- `norm_finitePlaceIdele_finitePlaceBaseUnitExtension`: for `x ∈ K_vˣ`, the norm of the one-place idele at `W` with component the image of `x` is the one-place idele at `v` with component `x ^ [L_W : K_v]`.
- `norm_finitePlaceIdele_eq_finitePlaceIdele_normUnits`: for any `y ∈ L_Wˣ`, `norm K L (finitePlaceIdele W y) = finitePlaceIdele v (normUnits K_v L_W y)`.
- `ideleClassNorm_finitePlaceIdeleClass_eq_normUnits`: the same identity for the classes in `C_L` and `C_K` under `ideleClassNorm`. The docstring calls this the norm–restriction input to the global reciprocity square.

## Proof

By the component formulas for the idele norm (`finiteComponent_norm_eq_prod`, `infiniteComponent_norm_eq_prod`), every factor except the one at `W` is `1`. For the first statement, the norm of an element of the base is its power by the degree (`normUnits_algebraMap_base`).

## Points to watch

- In the last two results `L_W` is a `K_v`-algebra through `finitePlaceAdicCompletionMap`, fixed by `let` in the statement; `normUnits` is the library's norm on unit groups.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/OnePlaceBaseNorm.lean`: the Lean file is the source byte for byte (SHA-256 `246f3650479df08fd7e5ff36a7f8af63dff94ea720e72202033ffea88b9a450b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
