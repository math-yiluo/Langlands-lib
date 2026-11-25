# Fixed fields of closed subgroups in the abstract class formation

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `Ω / k` be a Galois extension, possibly infinite. In the library's abstract class formation, fields are represented by closed subgroups of `Gal(Ω / k)`, and finiteness by finite quotients. This file passes to the concrete fixed fields: closed subgroups of finite index give finite extensions of `k`, and for closed subgroups `L ≤ K` with `L` normal in `K`, the quotient `K / L` is the Galois group of the fixed field of `L` over that of `K`, with matching degrees. The header calls this the field-theoretic input needed before the local class field axiom can be applied.

## Main definitions and results

- `abstractFixedField k Ω H`: the fixed field of a closed subgroup `H`. `closedFixingSubgroup_abstractFixedField_eq`: its fixing subgroup is `H` again (Mathlib's infinite Galois correspondence).
- `ambientQuotientFiniteOfAbstractFinite`, `abstractFiniteClosedSubgroup_isOpen`, `abstractFixedField_finiteDimensional`: if `H` has finite index in the abstract `baseField`, then `Gal(Ω / k) / H` is finite, `H` is open, and its fixed field is finite over `k`.
- `abstractFixedField_le`: `L ≤ K` gives an inclusion of fixed fields in the opposite direction.
- `abstractSubgroupEquivGaloisGroup`: `H ≃ Gal(Ω / F_H)`, where `F_H` is the fixed field of `H`.
- `abstractRelativeFixedField`: for `L ≤ K`, the fixed field `F_L` viewed as an intermediate field over `F_K`.
- `map_extensionSubgroup_abstractSubgroupEquiv`: the abstract relative subgroup corresponds to the subgroup fixing `F_L`.
- `abstractRelativeFixingSubgroup_normal` and `abstractRelativeFixedField_isGalois`: if `L` is normal in `K`, then `F_L / F_K` is Galois.
- `abstractRelativeToAmbientQuotient` with its kernel and surjectivity, `abstractExtensionQuotientEquivAmbient`, and `abstractExtensionQuotientEquivGaloisGroup`: an isomorphism `K / L ≃ Gal(F_L / F_K)`.
- `abstractFixedField_relativeFiniteDimensional` and `abstractRelativeFixedField_finiteDimensional`: if `K` has finite index over the base and `L` has finite index in `K`, then `F_L` is finite over `F_K`, in both presentations.
- `finiteAbstractExtension_degree_eq_finrank`: under normality and these finiteness conditions, the abstract degree of `L` over `K` equals `[F_L : F_K]`.

## Points to watch

- Normality and finiteness are explicit hypotheses (`hnormal`, `hKfinite`, `hLKfinite`); finiteness over the base is stated through the abstract quotient of `baseField`, not as finite index in the ambient group.
- Two presentations of the upper field occur: `abstractFixedField k Ω L` with an algebra structure over `F_K` given by inclusion, and `abstractRelativeFixedField`, obtained by extending scalars. The file proves finiteness for both.
- No local-field hypothesis appears; `k` and `Ω` may lie in different universes.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`: the Lean file is the source byte for byte (SHA-256 `99fa47ec007a84eb404ab2c06cd60a95e7a15c24ae0874f2f24cdfd3a59d1b45`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
