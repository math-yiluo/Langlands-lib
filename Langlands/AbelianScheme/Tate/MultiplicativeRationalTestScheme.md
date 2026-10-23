# Test-scheme naturality of rational and adelic Gm comparisons

For a fixed scheme `S` and morphism `a : T' ⟶ T` over `S`, the rational
Gm-to-roots comparison commutes with actual test-scheme restriction. The
declarations lie in `Langlands.GroupScheme.Gm.TateComparison`.

## Internal provenance

`MultiplicativeTestScheme` supplies both directions of the integral
comparison square. `RationalTestScheme` rationalizes actual test-scheme
restriction. The published `MultiplicativeRational` and
`MultiplicativeAwayRational` modules rationalize and bundle the actual
Gm-to-roots comparisons; `TwistRational` supplies maps induced by ring
homomorphisms on rational roots-of-unity limits. Tensor induction extends
the integral square to these rational maps. No additional claim is
attributed to original literature.

## Rational square and inverse

For any order predicate `P`, `rationalEquiv_testRestrict` states

```text
rationalEquiv T' P (Tate.rationalTestRestrict (Gm S).toGrp P a x) =
  TateTwist.Divisibility.rationalMap P a.left.appTop.hom
    (rationalEquiv T P x).
```

The ring map is the pullback on global sections from `T` to `T'`.
On pure tensors this is precisely `integralEquiv_testRestrict`; addition
extends the equality to every rational Tate element. The full comparison
is obtained by taking `P` constantly true, and the away comparison by
selecting orders coprime to the modulus.

`rationalEquiv_symm_testRestrict` is the inverse commuting square. Applying
the injective target comparison reduces it to the forward square and
the inverse identities.

## Adelic bundles

`finiteAdeleEquiv_testRestrict` and
`finiteAdeleEquiv_symm_testRestrict` give these two equalities using the
existing finite-adelic linear bundles. The same explicitly assumed
`Global.RationalProfiniteIntegerAdeleComparison` is used for both
comparisons, the restriction map and the root-induced map.

`primeToFiniteAdeleEquiv_testRestrict` and
`primeToFiniteAdeleEquiv_symm_testRestrict` give the away variants with
`Global.PrimeToRationalProfiniteIntegerAdeleComparison h m` explicit.
They use the same coupled witnesses on both sides. Their proofs reuse
the rational equalities because the adelic bundles leave the underlying
functions unchanged. The modulus is any natural number, without a
primality hypothesis.

## Scope

These are algebraic naturality equalities over a fixed base. They do not
assert rational continuity, a change-of-base theorem for group schemes,
geometric monodromy, rank, or a Weil pairing. The twist remains the
actual rational roots-of-unity limit and is not trivialized.
