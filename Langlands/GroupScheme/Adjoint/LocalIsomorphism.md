# Local isomorphisms induced on supplied adjoint quotients

This internal construction works over arbitrary fields `k` and `K` in the
same universe, with a `k`-algebra structure on `K`. It takes actual group
schemes `G`, `H`, `A`, `B` over `Spec k`, supplied full-centre adjoint quotient
maps `q : G ⟶ A` and `p : H ⟶ B`, and an actual natural local family
`e : LocalGroupIso G H (Over.mk (algebraBaseMap k K))`.
No finiteness, separability, perfectness or characteristic condition is imposed.

`IsAdjointQuotient.localIso` constructs a natural local family between `A`
and `B` over the same cover. The constructor first turns `e` into an actual
base-change isomorphism using `LocalGroupIso.toBaseChangeIso`. Field-extension
base change preserves the supplied adjoint quotients, so
`IsAdjointQuotient.mapIso` constructs an actual isomorphism of their targets
over `Spec K`. Applying `LocalGroupIso.ofBaseChangeIso` returns the desired
natural local family.

The general lemmas in `LocalGroupIso` describe evaluation on arbitrary
relative test schemes. The shared `coverPointsEquiv_comp`, imported from
`LocalGroupIsoBaseChangeEquivalence`, proves that the equivalence
between pullback points and original points over a chosen cover point commutes
with every group homomorphism. It uses naturality of `baseChangePointsEquiv`
and associativity of composition. `ofBaseChangeIso_square` then carries a
commutative square of actual base-change isomorphisms to the corresponding
square of local evaluations.

Applying those lemmas to the quotient square of `mapIso` proves
`IsAdjointQuotient.localIso_square`: for every relative test `T`, cover point
`a : T ⟶ Spec K`, and point `g : T ⟶ G`,

```text
localIso(a)(g followed by q) = e(a)(g) followed by p.
```

This uses the inverse law
`LocalGroupIso.ofBaseChangeIso_toBaseChangeIso` to recover the original family
`e`; it does not replace `e` with an independently chosen family.

`IsAdjointQuotient.localIso_innerAction` proves the corresponding equivariance
identity for the actual inner actions on every relative test:

```text
e(a)(innerAction_q(x, g)) =
  innerAction_p(localIso(a)(x), e(a)(g)).
```

An adjoint point need not lift to a point of the source group on its original
test scheme. The proof therefore uses
`AutomorphicAction.hom_ext_of_local_quotient_lift` with `q`. Flatness and
surjectivity come from the quotient witness, and the required affineness comes
from connected reductivity of `G` and adjointness of `A`. On the fpqc
pullback where `x` lifts to `h`, naturality of both local families and both
actions reduces the identity to the quotient square and
`innerAction_act_lift`. The two sides are conjugations by `e(a)(h)` and agree
by preservation of multiplication and inversion. The local-lift
extensionality lemma reflects that equality to the original test.

The provenance is internal: these are consequences of the existing actual
base-change, local-isomorphism, quotient and inner-action interfaces. The
module constructs local transport from supplied quotients and a supplied
local isomorphism. Constructing those initial data, a quasi-split model,
a finite Galois cover and an inner discrepancy remains part of the
unconditional inner-form existence problem.
