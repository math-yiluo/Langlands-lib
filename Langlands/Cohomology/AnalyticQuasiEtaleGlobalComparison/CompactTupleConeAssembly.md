# Compact compatible tuple cones

`compactCompatibleTupleCones` proves `CompactCompatibleTupleConesStatement ρ`.
For each positive tuple of a compact compatible cover, it constructs a wide
pullback cone in `QuasiEtaleSite X` with a compact Hausdorff vertex and an
`ActionLift ρ` on its structure map. The proof uses the field, space and
group universes of the statement independently, with an arbitrary topology
on the group.

The target and source actions are the cover's specified lifts restricted to
its common open subgroup. The subgroup inclusions preserve continuity of
the source actions. Applying the cover's twisted compatibility equation
at the inverse group element gives equivariance of each selected arrow
for the restricted actions.

The singleton cone has the selected source as its vertex and the identity
as its projection. At a successor, `compactContinuousRelativePullback`
pulls back the first arrow and the limiting tail cone's base arrow over
the cover target. This uses the inverse image of the target's analytic
diagonal in the full product over `X`. The relative pullback is compact
Hausdorff, lies in the site, and inherits a continuous action from that
product. The wide pullback limit follows by factoring through the tail and
then using the binary universal property. Both steps apply to arbitrary
test cones in the site. The recursion uses each entry of the tuple as
given, including repeated choices.

At each step the cone's base and all projections remain equivariant.
The triangle over `X` lets the base equation compose with the target
lift's structure-map equation. This gives `ActionLift ρ` on the
constructed vertex using the common open subgroup. Together with
compact Hausdorffness it places the vertex in `CompactLiftBasis ρ`.

The proof is an internal construction for the compact quasi-étale
comparison.
