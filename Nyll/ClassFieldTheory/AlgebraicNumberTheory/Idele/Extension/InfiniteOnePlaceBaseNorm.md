# Norms of ideles supported at one infinite place

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.InfiniteOnePlaceBaseNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K ⊆ L` be number fields, `W` an infinite place of `L` and `v` the place of `K` below it. A unit `x` of the completion `K_v` can be mapped into `L_W` and placed in the idele of `L` that is `x` at `W` and `1` elsewhere. The file computes the idele norm of this idele: it is the idele of `K` supported at `v` with component `x ^ [L_W : K_v]`.

## Main declarations

- `infinitePlaceBaseUnitExtension W : K_vˣ →* L_Wˣ`, induced by the completion map `NumberField.LiesOver.completionMap`; it sends `-1` to `-1` (`infinitePlaceBaseUnitExtension_neg_one`).
- `infinitePlaceCompletionDegree W`: the degree `[L_W : K_v]`.
- `norm_infinitePlaceIdele_infinitePlaceBaseUnitExtension`: the idele norm `IdeleGroup.norm K L` of the one-place idele at `W` with component the image of `x` is the one-place idele at `v` with component `x ^ [L_W : K_v]`.
- `..._of_isUnramified` and `..._of_isReal`: if `W` is unramified over `K`, in particular if `W` is real, the degree is 1 and the norm is the one-place idele of `x` itself.
- `ideleClassNorm_infinitePlaceIdeleClass_infinitePlaceBaseUnitExtension_of_isUnramified`, `..._of_isReal`: the same equalities for idele classes under `ideleClassNorm`.
- `ideleClassNorm_infinitePlaceIdeleClass_neg_one_of_isReal`: at a real place `W`, the class of `-1` at `W` has norm the class of `-1` at `v`.

## Proof

The component formulas for the idele norm (`infiniteComponent_norm_eq_prod`, `finiteComponent_norm_eq_prod`) leave a single nontrivial factor, the local norm at `W`. The norm of an element of the base is its power by the local degree (`normUnits_algebraMap_base`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/InfiniteOnePlaceBaseNorm.lean`: the Lean file is the source byte for byte (SHA-256 `4bdfdc02ff37e86dd7071e1bf8aa6ff442b44802c581994e17255baebd043ab9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
