# Full-order formal comparison for identity coefficient extension

This internal construction lifts the actual formal atlas comparison for
identity coefficient extension to the entire acting order. Its forward and
reverse maps retain exactly the previously constructed basic formal maps.
Both formal inverse equations and both complete compatible-family squares
hold for the full order-module maps.

## Scope and provenance

O and R are arbitrary commutative rings with a supplied O-algebra structure
on R. D is a possibly noncommutative O-algebra in an independent universe w.
The coordinate type is finite; the principal-generator cover may be infinite.
R and its coefficient tests have universe v and complete families have
universe v+1. E is an actual formal order action on the actual atlas X.
No noetherian, flatness or nontriviality hypothesis is imposed.

The module combines the internal `AtlasBaseChangeSelf` comparison with
`AtlasOrderBaseChangeAlong`. The full series for each order element are
compared using the supplied-target chart comparison, naturality of its
formal endomorphism along the identity test map, and equality of the chosen
source generator. No additional source theorem is asserted here; the
localization-gluing and order-action conventions are documented in
`BasicAtlas.md` and `AtlasOrderAction.md`.

This module concerns identity coefficient extension. It does not provide
successive supplied-map coherence, a specialness or height comparison,
framing, a varying-base moduli quotient or representability.

## Entire formal order-action comparison

All declarations are in
`Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction`.

For every R-test A, chart generator b that is invertible in A, and d in D,
`baseIdOrderChart_coordinates` proves that the action of d on the
identity-extended chart at `sourceChart X.baseIdOpens_eq b` has precisely the
coordinate series of the original action at b.

The proof begins with `baseChangeAlongOrderChart_coordinates`, which
identifies the extended action series with the original action at
`X.baseIdSource b` on the identity-restricted test. Naturality of the actual
formal endomorphism `E.endomorphism d` along `identityTestHom A` compares
that series to the action on the original test. Its underlying coefficient
map is `RingHom.id A`, so mapping coefficients changes nothing.
`X.baseIdSource_eq b` then identifies the original chart generator.
Thus the equality concerns every formal order-action series, beyond the
tangent action and the evaluated point function.

## Exact formal maps and their inverses

`baseIdHom E` is an actual order-linear formal map from
`E.baseChangeAlong (AlgHom.id O R)` to E, with cover equality
`X.baseIdOpens_eq`. Its underlying basic map is exactly `X.baseIdHom`, as
recorded by `baseIdHom_val`. Its commutation equation for every d reduces,
by extensionality of formal maps, to the complete coordinate comparison
above, since the formal chart maps have identity coordinates.

`baseIdInv E` similarly retains exactly `X.baseIdInv`, with the reversed
cover equality; `baseIdInv_val` is reflexivity. The same coordinate comparison
proves every reverse-map commutation equation after reindexing the chart.

`baseIdIso E` retains these two order-linear maps and proves both formal
inverse equations. Subtype extensionality reduces each inverse equation to
the corresponding equation of `X.baseIdIso`. Consequently this is an actual
formal order-linear isomorphism with formal inverse laws.

## Both complete-family squares

For every R-test A and every complete family x on its identity restriction,
`baseId_onPoints` states

```text
E.baseIdIso.onPoints A
  (E.baseChangeAlongPointEquiv (AlgHom.id O R) A x)
  = E.mapPoints (identityTestHom A) x.
```

The left route first extends the family along the identity coefficient
map, then evaluates the actual order-linear formal comparison. The right
route uses the identity underlying ring map from the restricted test to
the original test. Forgetting D gives precisely the existing basic-atlas
family square: the formal maps retain the original basic maps and
`baseChangeAlongPointEquiv_eq` identifies the family comparison functions.
The equation therefore applies to the entire family on every further test.
All three maps are linear over D.

`baseId_inv_onPoints` is the reverse square: the inverse linear equivalence
induced by the actual formal inverse takes
`E.mapPoints (identityTestHom A) x` back to the coefficient-extension family.
The proof uses `LinearEquiv.symm_apply_eq` and the forward square.
