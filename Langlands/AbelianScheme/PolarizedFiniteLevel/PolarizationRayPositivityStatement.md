# Positivity of integral proportionality between actual polarizations

`Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationRayPositivityStatement`
is a proposition in an arbitrary universe `u`. It is a statement target, not a
proof.

## Statement

It quantifies the named prerequisite package `P`, a scheme `S` with a proof
that `S` is nonempty, an actual abelian scheme `A` over `S` and a natural
number `g` with `0 < g` and `A.HasRelativeDimension g`. It then quantifies
dual witnesses `W` (the published `DualWitness` of `PolarizedFiniteLevel`)
and two actual homomorphisms `lam` and `lam'` from `A` to the constructed dual
`W.dual P`. Both are assumed to be polarizations in the published sense
`W.IsPolarization P`: each is an isogeny, and at every algebraically closed
point it is an ample Mumford map after some extension of the field.

The conclusion concerns integers `a ≠ 0` and `b` with `a • lam' = b • lam`
in the additive group of actual homomorphisms. It asserts `0 < a * b`. Thus
two polarizations on the same rational ray differ by a positive rational
factor. In particular a negative multiple of a polarization is never a
polarization when the relative dimension is positive. When `b = 0` the
hypotheses cannot hold, because `lam'` would vanish and a zero map of a
positive-dimensional abelian scheme is not an isogeny.

## Role and provenance

This is an internal target. It records the standard positivity of
polarizations: over an algebraically closed field, if `M` and `L` are ample
and `b φ_L = a φ_M`, then the ratio `b / a` is positive. It is needed by Task
3269. The ordinary Harris relation `TateNormalizedCMOrdinaryRelated` allows an
arbitrary rational multiplier `q`, and the primitive normalized polarization
`HarrisPrimitivePolarization` is invariant along the relation only when `q`
is positive.

A possible proof reduces to one geometric point of the nonempty base. It then
uses one of two routes. The first: the Library's ampleness of tensor products
and of positive tensor powers shows that a positive combination of
polarizations is a polarization, hence an isogeny, whereas a negative ratio
would make some positive combination vanish. The second compares Euler
characteristics of ample and anti-ample bundles. The positive dimension
hypothesis is necessary: over a zero-dimensional abelian scheme the zero map
and its negative are both polarizations.

The relative dimension convention is the published
`AbelianScheme.HasRelativeDimension`, i.e. smoothness of the structure
morphism of relative dimension `g`.
