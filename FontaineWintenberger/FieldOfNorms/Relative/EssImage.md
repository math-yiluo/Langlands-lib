# The essential image of the field-of-norms functor

Module `FontaineWintenberger.FieldOfNorms.Relative.EssImage`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field, `L/K` an infinite separable APF extension and `Ω` a separable closure of `L`. The file shows that every separable algebraic extension of the norm field `FieldOfNorms K L` is, up to isomorphism over that field, the relative field of norms `RelFieldOfNorms K L M` of an intermediate field `M` of `Ω/L`, and that finite extensions correspond to finite `M`. This is the essential surjectivity in Wintenberger's Theorem 3.2.2.

## Main results

Finite Galois stages (`P/L` finite Galois, `P/K` infinite APF):

* `FieldOfNorms.mem_range_inclusion_fixedField_iff`: for a subgroup `H` of `P ≃ₐ[L] P`, an element of `FieldOfNorms K P` comes from the norm field of the fixed field of `H` exactly when it is fixed by the action of `H`.
* `FieldOfNorms.exists_fixedField_inclusion_range`: every intermediate field of `FieldOfNorms K P` over `FieldOfNorms K L` is the image of the norm field of a fixed field of some subgroup `H`.

Subfields of the limit, for `Ω` a separable closure of `L`:

* `RelFieldOfNorms.exists_finite_subfield_preimage`: every intermediate field `D` of `RelFieldOfNorms K L Ω`, finite over `FieldOfNorms K L`, is the range of `RelFieldOfNorms.ofAlgHom N` for some finite `N` in `Ω/L`.
* `RelFieldOfNorms.finiteImage_le_iff`, `RelFieldOfNorms.finiteImage_injective`: `N ↦ RelFieldOfNorms.finiteImage N` preserves and reflects inclusion, hence is injective. `RelFieldOfNorms.existsUnique_finite_subfield_preimage` combines these.
* `RelFieldOfNorms.exists_subfield_preimage`: every intermediate field `D` of `RelFieldOfNorms K L Ω` is the range of `RelFieldOfNorms.algMap` of the inclusion `M → Ω` for some intermediate field `M`.

Essential image:

* `exists_finite_fieldOfNorms_algEquiv_of_separableClosure`, `exists_finite_fieldOfNorms_algEquiv`: every finite separable extension `F` of `FieldOfNorms K L` is isomorphic over it to `FieldOfNorms K N` for a finite `N` in `Ω/L` (respectively in `SeparableClosure L`).
* `exists_relFieldOfNorms_algEquiv_of_separableClosure`, `exists_relFieldOfNorms_algEquiv`: every separable algebraic extension `F` of `FieldOfNorms K L` is isomorphic over it to `RelFieldOfNorms K L M` for an intermediate field `M`.

A helper, `FiniteIntermediateField.exists_le_of_le_directed_iSup`, says that a finite subextension of a directed union of intermediate fields lies in one member.

## Proofs

`F` is embedded in `RelFieldOfNorms K L Ω`, which is separably closed (`RelFieldOfNorms.isSepClosed`, from `FontaineWintenberger.FieldOfNorms.Relative.SeparablyClosed`). A finite subfield `D` of the limit factors through one stage (`RelFieldOfNorms.exists_algHom_factor`); enlarging that stage to its normal closure `P`, the Galois correspondence for `FieldOfNorms K P` over `FieldOfNorms K L` (`FieldOfNorms.isGaloisGroup`) identifies `D` with the image of the fixed field of a subgroup. Reflection of inclusions uses `RelFieldOfNorms.autEquiv_mem_fixingSubgroup_iff` and the infinite Galois correspondence for `Ω/L`. For arbitrary `D`, the field `M` is the directed supremum of the unique finite preimages of the finite subfields of `D`.

## Remarks

The isomorphisms are asserted to exist (`Nonempty`), not constructed canonically.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Relative/EssImage.lean` (SHA-256 of the source file `049289beb39fbb6dc8f83d49e393e090cbe7753bc229869e2cee620a0f4e9182`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
