# Galois-fixed units of an intermediate field

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the abstract class formation used for local reciprocity, the coefficient module is the unit group `Ωˣ` of a Galois extension `Ω / K`, with its Galois action. For an intermediate field `E`, this file identifies the subgroup of `Ωˣ` fixed by the closed subgroup `Gal(Ω / E)` with the image of `Eˣ`. The extension `Ω / K` may be infinite; the intended case is `Ω = SeparableClosure K`.

## Main definitions and results

- `galoisAmbientUnitsRep K Ω`: the representation of `Gal(Ω / K)` on `Ωˣ`, written additively, as a `Rep ℤ` (an abbreviation for Mathlib's `Rep.ofAlgebraAutOnUnits`).
- `intermediateFieldUnitsToGaloisAmbient K Ω E`: the inclusion `Eˣ → Ωˣ` in additive notation, with its evaluation lemma.
- `mem_galoisAmbientUnits_fixed_iff`: for `[IsGalois K Ω]`, a unit of `Ω` is fixed by `closedFixingSubgroup K Ω E` exactly when it lies in `E`. This rests on Mathlib's infinite Galois correspondence, `InfiniteGalois.fixedField_fixingSubgroup`.
- `intermediateFieldUnitsToGaloisAmbient_range`: the image of `Eˣ` is exactly the fixed subgroup `ambientFixedAddSubgroup` used by the abstract framework.
- `intermediateFieldUnitsEquivGaloisFixed`: the resulting isomorphism from `Eˣ` onto the fixed subgroup, with a lemma computing its values.
- `embeddedFieldUnitsEquivGaloisFixed K Ω L i`: for a `K`-embedding `i : L → Ω`, an isomorphism from `Lˣ` onto the subgroup fixed by `Gal(Ω / i(L))`, obtained by composing with `L ≃ i(L)`.

## Points to watch

- No local-field, perfectness or finite-dimensionality hypothesis is made; only `Ω / K` Galois. The header explains why the separable closure, not the algebraic closure, is the right ambient field: for an imperfect `K`, the fixed field of `Aut(K^alg / K)` in `K^alg` need not be `K`.
- The fixed subgroup is taken for `closedFixingSubgroup K Ω E`, the library's closed-subgroup packaging of `Gal(Ω / E)`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean`: the Lean file is the source byte for byte (SHA-256 `927c943c2a8603d05d0bed7e4ea355ec7a621e04263e5346e065ea333d3f3965`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
