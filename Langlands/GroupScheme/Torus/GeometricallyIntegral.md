# Tori over a field are geometrically integral

Worker 1424.

`IsTorus.geometricallyIntegral`: if `T` is a torus over `Spec k` for a field
`k` (the published predicate `IsTorus` of `Torus/Lattice.lean`), then the
structure morphism `T.X.hom` is geometrically integral in Mathlib's sense
(`GeometricallyIntegral`): its base change along `Spec K ⟶ Spec k` is an
integral scheme for every field extension `K` of `k`. This is the standard
fact that a torus is a geometrically integral variety. It is an internal
consequence of two published Library results, so no literature locator is
needed.

## Proof

Mathlib's `geometricallyIntegral_iff` and `geometrically_iff_of_commRing`
reduce the claim to the following. For every field `K` that is a `k`-algebra
and every pullback square of `T.X.hom` along `Spec K ⟶ Spec k`, with apex `Y`,
the scheme `Y` is integral.

The published `IsTorus.baseChange` says that the base change of `T` to `K` is
again a torus. The published `IsTorus.isIntegral` (`Torus/Integral.lean`) says
that the underlying scheme of a torus over a field is integral. Together they
show that the chosen pullback `pullback T.X.hom (Spec.map (algebraMap k K))` is
integral. The given square is a pullback square, so its apex `Y` is isomorphic
to this chosen pullback by `IsPullback.isoPullback`. Integrality transfers
along this isomorphism by `IsIntegral.of_isIso`.

The variant `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` is not
used, because Mathlib has no `IsClosedUnderIsomorphisms` instance for the
integrality predicate. The isomorphism is applied by hand instead.
