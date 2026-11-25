# Idele classes of abstract fixed fields in the rational representation

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitAbstractFixedField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the rational absolute class formation, a closed subgroup of `Gal(ℚˢᵉᵖ/ℚ)` plays the role of a field. The file identifies the fixed part of `rationalIdeleClassRepresentation` under such a subgroup with the idele class group of its actual fixed field, for the base subgroup, for finite-index closed subgroups and for relative fixed fields.

## Main definitions

- `rationalIdeleClassEquivBaseFixed`: `C_ℚ` is additively equivalent to the fixed part at `baseField` (the whole group). It is `rationalIdeleClassEquivFixed` at the bottom intermediate field `⊥`, transported along `ℚ ≃ ⊥` and the identity `Gal(ℚˢᵉᵖ/⊥) = baseField`.
- `rationalAbstractFixedFieldIdeleClassEquivFixed K`: for a closed subgroup `K` of finite index (given as finiteness of the quotient of the base by `K`), the idele class group of `abstractFixedField ℚ ℚˢᵉᵖ K` is equivalent to the fixed part at `K`.
- `rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional K L hLK`: for `L ≤ K`, the idele class group of the relative fixed field of `L` is equivalent to the fixed part at `L`.

## Main results

- `rationalIdeleClassEquivFixed_extension_coe`: for finite intermediate fields `F ≤ E`, a relative idele class of `F` and its scalar extension to `E` have the same image in the direct limit; the comparison turns scalar extension into inclusion of fixed parts.
- `rationalIdeleClassEquivBaseFixed_coe`: for every finite Galois level `E`, the underlying direct-limit element of the image of a rational idele class `c` under `rationalIdeleClassEquivBaseFixed` is the image under `rationalRelativeIdeleClassToDirectLimit E` of the diagonal class `RelativeIdeleGroup.classInclusion ℚ E c`.
- `rationalAbstractFixedFieldIdeleClassEquivFixed_coe` (simp): the closed-subgroup version has the same underlying direct-limit element as `rationalIdeleClassEquivFixed`.

A local instance gives finite dimensionality of the fixed field of a finite-index closed subgroup.

## Points to watch

- The equivalences are transports of `rationalIdeleClassEquivFixed` along the equality between a closed subgroup and the fixing group of its fixed field, which comes from another file.
- The relative version does not derive finiteness: it takes `FiniteDimensional ℚ` and `NumberField` of the relative fixed field as instance hypotheses.
- The equivalences are stated on the additive form `Additive (IdeleClassGroup _)`; `rationalIdeleClassEquivFixed_extension_coe` and `rationalIdeleClassEquivBaseFixed_coe` take multiplicative classes and apply `Additive.ofMul`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/IdeleClassDirectLimitAbstractFixedField.lean`: the Lean file is the source byte for byte (SHA-256 `abb9b1de65383d63749f31b3b65efe6d12a7aeba521e0a8e2caab742c66ded68`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
