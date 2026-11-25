# S-ideles and S-units of a number field

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.SPlaces`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K` and a set `S` of finite places, this file defines the subgroup `I_K^S` of ideles whose finite components are local units outside `S`, its finite-idele counterpart, and the group of `S`-units of `K`.

## Main definitions and results

- `FiniteIdeleGroup.supportedAt S`: finite ideles `a` with `a_v` a unit of the valuation ring of `K_v` for every finite place `v ∉ S`. The subgroups grow with `S`; every finite idele lies in one with `S` finite (`exists_finset_supportedAt`), so their supremum over finite `S` is everything (`iSup_finset_supportedAt`); for `S = ∅` one gets the everywhere-integral subgroup `integralSubgroup`; for finite `S` the subgroup is open (`isOpen_supportedAt`).
- `IdeleGroup.supportedAt S`: the preimage of the previous subgroup under the projection of the idele group to the finite ideles, so the archimedean components are unrestricted. The same results are proved: monotonicity, exhaustion by finite `S`, equality with `integralAtFinitePlaces` for `S = ∅`, and openness for finite `S`.
- `SUnitGroup S`: for a finite set `S` of finite places, Mathlib's group `Set.unit K` of `S`-units; `mem_SUnitGroup_iff` says that `x ∈ Kˣ` is an `S`-unit when its `v`-adic valuation is `1` at every finite `v ∉ S`.

## Proof

Finiteness of the exceptional set is the restricted-product condition on a finite idele; openness follows from openness of the local unit groups and Mathlib's criterion for sets of the form "component in an open set outside `S`" in a restricted product.

## Points to watch

- `S` records only finite places: every archimedean place is always treated as lying in `S`, both for `I_K^S` and for the `S`-units. This differs from the convention in which `S` is a set of all places containing the archimedean ones.
- `supportedAt` accepts any set `S`, not only finite ones; openness is proved only for finite `S`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/SPlaces.lean`: the Lean file is the source byte for byte (SHA-256 `5f64be485a6000409e0647ac6311209c0c4b9edae8ec71fe87bfc0569c86ace0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
