# Relative H² transport across independent field universes

This module constructs `relativeH2Equiv e`, an additive equivalence

```
relativeCohomology K L 2 ≃+ relativeCohomology K M 2
```

from an actual `K`-algebra equivalence `e : L ≃ₐ[K] M`. The fields have
independent universes: `K : Type u`, `L : Type v`, and `M : Type w`.
Only the field and indicated algebra instances are assumed; finiteness,
normality, local-field structure, and a supplied cohomology equivalence are
not assumptions.

## Cochains and the actual Galois actions

Write `pₑ(s) = e.symm ∘ s ∘ e` for an automorphism `s` of `M` over `K`.
`relativeAutPullback e` is this group homomorphism from `Gal(M/K)` to
`Gal(L/K)`, with its pointwise formula and inverse-conjugation identity
proved in `relativeAutPullback_apply` and
`relativeAutPullback_symm_apply`.

`relativeUnitTransport e` is the additive equivalence on `Additive Lˣ`
and `Additive Mˣ` induced by the actual field map on units. Its underlying
field value is `e` applied to the original unit value. The lemmas
`relativeUnitTransport_symm_apply` and `relativeUnitTransport_action`
prove the inverse identity and equivariance with the unchanged
`unitsRepresentation` actions.

`relativeCochainOneTransport` transports a one-cochain `b` by
`b ↦ (s ↦ e_*(b(pₑ(s))))`. The additive homomorphism
`relativeCochainTwoTransport` transports a two-cochain `z` by

```
(s, t) ↦ relativeUnitTransport e (z (pₑ(s), pₑ(t))).
```

`relativeCochainTwoTransport_d₁₂` proves that this formula commutes with
the degree-one coboundary differential, using additivity and the action
identity. Consequently, `relativeCochainTwoTransport_mem_coboundaries`
shows that a coboundary with primitive `b` maps to a coboundary with the
explicit primitive `relativeCochainOneTransport e b`.

The public additive homomorphism `relativeCocycleTransport e` restricts
the same formula to actual two-cocycles. Its membership proof applies the
unit equivalence to the source cocycle identity and uses conjugation's
multiplicativity and equivariance. `relativeCocycleTransport_apply`
is the displayed formula on cocycles. Its inverse identity,
`relativeCocycleTransport_symm_apply`, follows pointwise from the inverse
identities for conjugation and units.

## Descent to the existing cohomology and the inverse

The imported definitions `relativeCohomology` and `unitsRepresentation`
are unchanged. In particular, the source scalar ring is
`IntegerScalars.{v}` and the target scalar ring is `IntegerScalars.{w}`.
The construction uses additive homomorphisms and does not require these
rings to have a common universe.

`relativeCocycleTransport_H2π_eq` proves independence of the cocycle
representative. Mathlib's `H2π_eq_iff` identifies equality of two classes
with their cocycle difference being a coboundary, and the explicit
coboundary transport above preserves that condition.

The private representative construction uses `H2_induction_on` to prove
that every cohomology class is represented by a two-cocycle, then chooses
such a representative. `relativeH2Transport` sends its class to the class
of the explicitly transported representative. Independence of the choice
proves `relativeH2Transport_H2π`; induction on representatives proves
additivity. Choice is used only to select representatives, not to select
an abstract equivalence between cohomology groups.

`relativeH2Transport_symm_apply` proves that transport along `e.symm`
after transport along `e` is the identity, by induction on `H2π`
representatives and the cocycle inverse identity. Applying the same
argument to `e.symm` gives the other inverse. These are the two inverse
proofs in `relativeH2Equiv`. The public representative formula is

```
relativeH2Equiv e (groupCohomology.H2π (unitsRepresentation K L) z) =
  groupCohomology.H2π (unitsRepresentation K M) (relativeCocycleTransport e z).
```

It is proved as `relativeH2Equiv_H2π`. The equality
`relativeH2Equiv_symm` identifies its inverse with `relativeH2Equiv e.symm`.

## Provenance and scope

This is internal derived content: explicit functoriality of the ordinary
inhomogeneous two-cocycle quotient under a field isomorphism. It derives
from the Library's `Local.Cohomology` definitions and Mathlib's
`RepresentationTheory/Homological/GroupCohomology/LowDegree.lean` API,
specifically `mem_cocycles₂_iff`, `d₁₂_hom_apply`, `H2π_eq_iff`, and
`H2_induction_on`. It invokes no external arithmetic theorem.

No absolute restriction compatibility, local invariant, arithmetic
normalization, or H² existence theorem is asserted.
