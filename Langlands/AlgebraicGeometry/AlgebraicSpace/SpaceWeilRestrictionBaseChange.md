# Base change of Weil restrictions on all test schemes

Author: Worker 113.

This is an internal categorical construction supporting the local comparison
in the adelic Weil-restriction proof. It constructs the base-change
isomorphism for the full presheaves, then packages it for algebraic spaces
when representability of both restrictions is given.

Let

```text
T' --f'--> S'
 |          |
 g'         g
 |          |
 v          v
T  --f---> S
```

be a cartesian square of actual schemes. For a scheme `U` over `T`, pasting
the defining square of `U ×_T T'` with the given square shows that
`U ×_T T'`, viewed over `S'`, is the pullback of `U → T → S` and
`S' → S`. The canonical comparison is therefore an isomorphism
`U ×_T T' ≅ U ×_S S'` over `S'`.

`WeilRestrictionBaseChange.testPullback` implements this pasting.
`testIso` uses the resulting pullback universal property to compare with
Mathlib's chosen pullback. Its two projection laws specify the map to `U`
and the map to `S'`. `testNatIso` proves that these comparisons are
natural in all schemes over `T`, by testing equality on the two pullback
projections.

For any presheaf `P` on schemes over `S'`,
`weilRestrictionBaseChangePresheafIso` applies the contravariant functor
`P` to this natural isomorphism. Its source is restriction to `T` of
the Weil presheaf along `g`; its target is the Weil presheaf along `g'`
of the restriction of `P` to `T'`. The component lemma states that the
forward map is exactly pullback along `testIso.hom`. This is an
isomorphism on the entire category of test schemes, rather than only on
field points or affine points.

`weilRestrictionBaseChangeSpaceIso` packages that presheaf isomorphism
as an isomorphism of algebraic spaces. It takes an algebraic space `X'`
over `S'`, a witness that its restriction along `g` is algebraic, and
a witness that the restriction along `g'` of its base change to `T'`
is algebraic. Its source is the base change to `T` of the first
restriction, and its target is the second restriction.

No finiteness, flatness, separatedness or finite-type assumptions enter
the presheaf comparison. The algebraic-space construction keeps both
representability witnesses explicit and does not prove a representability
theorem or a topological comparison.

Provenance is internal: the result follows from Mathlib's pullback
pasting and uniqueness properties and the definitions of
`weilRestriction` and `baseChange` in the Library. It provides a
structural identity needed when applying a local Weil comparison to a
base change of a global algebraic space.
