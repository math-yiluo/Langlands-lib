# Norms of power-local-unit idèle subgroups

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.KummerNormDescent`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension `L/K` of number fields, the file shows that the idèle norm carries the library's power-local-unit subgroup of `L` into the corresponding subgroup of `K`, and deduces the same for idèle classes. The module docstring gives the purpose: descending idèle-class norm statements when a Kummer extension is first built over a finite extension of the base and then viewed over the original field.

## Main results

`idelePowerLocalUnitSubgroup n S T` is a subgroup of the idèle group defined in an imported file. As used in the proofs here, with `T = ∅`, its elements are the idèles whose components are `n`-th powers at every infinite place and at every finite place in `S`, and integral units at every other finite place.

- `ideleNorm_mem_powerLocalUnitSubgroup_of_supports_above`: let `n : ℕ+`, `S` a finite set of finite places of `K` and `S'` one of `L`, and suppose `hS`: a place `W` of `L` lies in `S'` exactly when the place of `K` below it lies in `S`. If `a` is in `idelePowerLocalUnitSubgroup n S' ∅` over `L`, then `IdeleGroup.norm K L a` is in `idelePowerLocalUnitSubgroup n S ∅` over `K`.
- `ideleClassNorm_map_powerLocalUnitSubgroup_le_of_supports_above`: under the same hypothesis, the image of `ideleClassPowerLocalUnitSubgroup n S' ∅` under `ideleClassNorm K L` lies in `ideleClassPowerLocalUnitSubgroup n S ∅`.

## Proof

The component of the norm at a place of `K` is the product of the local norms of the components at the places above it (`IdeleGroup.infiniteComponent_norm_eq_prod`, `IdeleGroup.finiteComponent_norm_eq_prod`). The local norm `LocalFieldTheory.normUnits` is multiplicative, so it sends `n`-th powers to `n`-th powers. Outside `S` the places above lie outside `S'`, and the local norm of an integral unit is an integral unit (`IdeleGroup.finitePlace_normUnits_mem_integerUnits`). The idèle-class statement follows by choosing idèle representatives.

## Points to watch

- `S'` must be exactly the set of places of `L` above `S`, as an equivalence, not just an inclusion.
- Both results are stated only with the second set of places of the subgroup empty.
- `L/K` need only be finite; no Galois hypothesis is made.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/KummerNormDescent.lean`: the Lean file is the source byte for byte (SHA-256 `700012d913253fcfe39337d1bb55c04d1f667bebd49445ecc0300b8e1c1fd4aa`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
