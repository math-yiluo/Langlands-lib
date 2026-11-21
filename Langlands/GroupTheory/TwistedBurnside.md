# Twisted Burnside counting

`Langlands.TwistedBurnsideStatement` is a finite-group counting proposition.
Let `G` act on any type `X`, and let `F : X → X` send elements in the same
orbit to elements in the same orbit. Then `F` descends to the orbit quotient
`X/G`, and the proposition is
\[
  \sum_{g\in G} \#\{x\in X:g\cdot F(x)=x\}
    = |G|\,\#\{o\in X/G:F(o)=o\}.
\]
The cardinalities are extended natural numbers; no finiteness is required of
`X` or of the fixed-point or fixed-orbit sets. The map need not be invertible.

**Internal provenance.** This extends the incidence formulation of ordinary
Burnside counting (`MulAction.sigmaFixedByEquivOrbitsProdGroup`, the case
`F = id`). It isolates the group-action count used in the tame averaging
route: in that application `F` is a lift of Frobenius acting on wild
inertia classes and `G` is a finite quotient of inertia. Over a fixed orbit,
the elements carrying `F(x)` to `x` form a translate of a stabilizer, so the
incidence fibre has size `|G|` by orbit–stabilizer. This module states the
abstract identity only; it asserts no local field or representation comparison.
