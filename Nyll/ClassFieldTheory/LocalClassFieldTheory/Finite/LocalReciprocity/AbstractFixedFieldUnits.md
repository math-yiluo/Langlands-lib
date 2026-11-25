# Units of fixed fields as Galois representations in a tower of closed subgroups

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `Ω / k` be a Galois extension, possibly infinite, and let `L ≤ K` be closed subgroups of `Gal(Ω / k)` with `L` normal in `K`. The library's abstract class formation attaches to this tower a representation of `K / L` on the `L`-fixed units of `Ω` (`extensionFixedRepresentation`). This file identifies it, action included, with the natural representation of the relative Galois group on the units of the fixed field of `L`, viewed as an extension of the fixed field of `K`. The header notes that comparing the action, not only the underlying groups, is what allows the Tate groups themselves to be transported.

## Main definitions and results

- `abstractFixedFieldUnitsEquivGaloisFixed k Ω H`: for any closed subgroup `H`, an additive isomorphism between the units of the fixed field of `H` and the `H`-fixed units of `Ω`.
- `abstractRelativeFixedFieldUnitsEquivGaloisFixed`: the same for the upper fixed field `abstractRelativeFixedField k Ω hLK`, seen over the lower one.
- `abstractExtensionFixedRepresentationUnitsEquiv`: the comparison of underlying groups, from the abstract representation to the units of the upper fixed field; `abstractRelativeUnitsEquiv_extensionUnitsEquiv` relates it to the library's `extensionFixedRepresentationEquiv`.
- `abstractExtensionQuotientEquivGaloisGroup_mk_apply_val`: for `σ ∈ K`, the relative Galois automorphism attached to the coset of `σ` acts on the upper fixed field as `σ` itself does.
- `relativeCosetAction_abstractRelativeFixedFieldUnit_val` and `abstractExtensionFixedRepresentationUnitsEquiv_action`: the comparison carries the abstract coset action to the Galois action.
- `abstractExtensionFixedRepresentationIsoUnitsRes`: an isomorphism in `Rep ℤ` between `extensionFixedRepresentation` and the unit representation `Rep.ofAlgebraAutOnUnits`, restricted along the isomorphism `abstractExtensionQuotientEquivGaloisGroup` from `K / L` to the relative Galois group.

## Proof

The action comparison reduces, on coset representatives, to the fact that the relative automorphism is obtained by restricting `σ` (`AlgEquiv.restrictNormalHom`), using Mathlib's infinite Galois theory (`InfiniteGalois.normalAutEquivQuotient`).

## Points to watch

- Here `K` and `L` name closed subgroups of the Galois group; the ground field is `k`.
- Normality of `L` in `K` is the explicit hypothesis `hnormal`, installed by a `let` inside the statements.
- Although the header speaks of a finite tower, no statement in this file assumes that `L` has finite index in `K`, and nothing local is assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean`: the Lean file is the source byte for byte (SHA-256 `47a1344295219fc5b095f9efcdb9b0177d8f8878b72e0152a019a24cb12dd196`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
