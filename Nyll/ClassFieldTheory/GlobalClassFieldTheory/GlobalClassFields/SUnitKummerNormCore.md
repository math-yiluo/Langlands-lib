# S-unit Kummer extensions and power quotients of the idèle class group

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SUnitKummerNormCore`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a number field containing the `n`-th roots of unity. The file enlarges a finite set `S` of finite places to a set `S'` containing the primes dividing `n` and supporting representatives of all idèle classes. For this `S'` it identifies the principal idèles satisfying the local `n`-th power conditions with the `n`-th powers of `S'`-units, and shows that the corresponding power quotient of the idèle class group has the order of the Galois group of the full `S'`-unit Kummer extension. The module docstring calls these cardinality ingredients of the existence theorem.

## Main definitions and results

- `even_or_no_realInfinitePlace_of_primitiveRoots`: if `K` has a primitive `n`-th root of unity and `n > 1`, then `n` is even or `K` has no real place.
- `sUnitKummerNormSupport n S`: the union of `S`, a fixed finite set on which supported idèles and principal idèles generate the idèle group, and a finite set outside which `n` is a unit. Lemmas record that it contains `S` and every prime dividing `n`, and that it inherits the generation property.
- `principalIdelePowerLocalUnitSubgroup_eq_sUnitNthPowers_on_kummerNormSupport`: assume `n`-th roots of unity lie in `K`. Then an element of `Kˣ` whose principal idèle is an `n`-th power at the infinite places and at `S'`, and a unit outside `S'`, is an `S'`-unit that is an `n`-th power in `Kˣ`, and conversely.
- `card_ideleClassPowerLocalUnitQuotient_on_kummerNormSupport`: the power quotient `IdeleClassPowerLocalUnitQuotient n S' ∅` has order `n ^ totalPlaceCard S'`, where `totalPlaceCard` is the library's count of places attached to `S'`.
- `card_ideleClassPowerLocalUnitQuotient_eq_finrank_fullSUnitKummerExtension`: this order equals the degree over `K` of `fullSUnitKummerExtension n S'`, built inside a separable closure `Omega` of `K`.

## Proofs

If `b` satisfies the local conditions, its Kummer extension `M = K(b^(1/n))` splits completely at `S'`, has every local element at infinite places as a norm, and is unramified outside `S'`. So every idèle class is a norm from `M`, and the imported equality of the norm index with the degree for abelian extensions gives `[M : K] = 1`. The order formula combines an imported product formula, `n ^ (2 · totalPlaceCard S')` for the product of two quotient orders, with the order of `S'`-units modulo `n`-th powers.

## Points to watch

- Everything is stated for the enlarged set `sUnitKummerNormSupport n S`, not for `S` itself, and only with the second set of places of the power subgroups empty.
- The roots of unity hypothesis is `(primitiveRoots n K).Nonempty`.
- The identification of principal idèles rests on the imported equality of the norm index with the degree, an input from reciprocity.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/SUnitKummerNormCore.lean`: the Lean file is the source byte for byte (SHA-256 `e8e7698a3d2e5487092e0c67d5abf99070b03b1295cb7ec42186208076d71306`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
