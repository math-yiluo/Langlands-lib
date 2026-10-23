# Equivalences and finiteness from relative invariant images

Author: Worker 21.

This module packages consequences of the existing predicate
`InvariantFamily.RelativeImages`. Fix a prime `p`, an arbitrary family
`I : InvariantFamily.{u,v} p`, and a proof `hI : I.RelativeImages`.
For a base `F : PadicField.{u} p` and a field `L : Type v`, assume the
specified algebra `F.Carrier → L` is finite dimensional and Galois.
Write `d = Module.finrank F.Carrier L`; its positivity follows from
`Module.finrank_pos`. The universes `u` and `v` are independent.

The source throughout is the published actual group
`relativeCohomology F.Carrier L 2`, with the Galois action on `Lˣ`.
The target `RationalModIntegers` is the actual quotient of the rationals by
the integers, and `denominatorSubgroup d` is its subgroup annihilated by `d`.
No replacement of these groups or of the supplied family occurs.

## Constructions and formulas

`relativeInvariantEquiv` restricts the codomain of `I.relative F L` to
`denominatorSubgroup d`. The range equality in `hI F L` proves membership.
Injectivity is the first part of that same hypothesis; surjectivity follows
by taking a preimage of each subgroup element using the range equality.
`AddEquiv.ofBijective` bundles this map as an additive equivalence.

`relativeInvariantEquiv_apply` states that its value, included in the
rational quotient, is exactly `I.relative F L x`.
`relativeInvariantEquiv_symm_apply` states that applying the supplied
invariant to the inverse image of a subgroup element recovers that element.
The former is definitional; the latter follows by applying subtype
projection to the inverse identity.

`relativeZModEquiv` composes this equivalence with the inverse of the
published `denominatorEquiv d Module.finrank_pos`, yielding

```text
relativeCohomology F.Carrier L 2 ≃+ ZMod d.
```

`denominatorEquiv_relativeZModEquiv` recovers the supplied invariant by
mapping the cyclic coordinate through `denominatorEquiv` and subgroup
inclusion. Its proof cancels the denominator equivalence with its inverse.
For any integer `z`, `relativeZModEquiv_symm_intCast` states that the
invariant of the inverse image of `(z : ZMod d)` is the class of `z/d`.
It follows from the inverse-image formula and `denominatorEquiv_intCast`,
including for negative integers and `d = 1`.

## Cardinality and scope

`relativeH2_card` proves that the natural cardinality of actual relative
`H²` is `d`, by invariance of cardinality under `relativeZModEquiv` and
`Nat.card_zmod`.
`relativeH2_finite` separately supplies `Finite` for this group:
the cardinality formula and positivity of `d` give a nonzero natural
cardinality, and `Nat.finite_of_card_ne_zero` gives finiteness.
Thus the cardinality result is not being used as an inequality that could
also hold merely because the natural cardinality of an infinite type is zero.

These are conditional constructions for an arbitrary supplied invariant
family. They do not establish `RelativeImages`, construct a local invariant
family, or prove the global invariant existence statement. They require
neither arithmetic normalization nor any tower compatibility law.

## Provenance

This is a derived internal package from the published
[`Invariants`](Invariants.md) definition of `RelativeImages` and
[`UnramifiedInvariant`](UnramifiedInvariant.md) construction
`denominatorEquiv`. Although the latter module also contains unramified
arithmetic constructions, its denominator equivalence is elementary
quotient-group algebra and requires only `0 < d`. No unramified hypothesis
is imposed here. The new arguments are codomain restriction, composition of
additive equivalences, and transport of finite cardinality. They use these
published declarations by Lean name and preserve every imported pair.
