# Actual isomorphisms between full Tate-normalized Harris CM models

Author: Worker 344.

This internal comparison works with two existing
`TateNormalizedCMRepresentative` values over the same connected admissible CM
base, geometric point and original Harris level. The Hodge image of that level
must preserve the fixed Harris integral source span. Both models retain their
actual abelian schemes, polarizations, rational algebra actions, integral order
actions, determinant and geometric dimension conditions, and original fixed
level orbits.

`tateNormalizedCMIso_full_image_iff` starts with the original rational
action isomorphism `e`, rational multiplier `q`, its original geometric
polarization equation, and the exact equation transporting the first original
level to the second. At a source-stabilizing level the existing carried-lattice
criterion identifies each model's lattice with its full integral Tate
rationalization image. The original rational Tate map preserves and reflects
membership in these carried lattices. Substitution of the original level
equation therefore proves preservation and reflection for the full integral
Tate images themselves.

For `tateNormalizedCMIso_integral`, the point field is algebraically closed.
Its characteristic zero follows from its actual map to the CM-field base. The
preceding membership equivalence supplies the two full-image hypotheses of the
published `Tate.connectedIntegralLatticeReflection` theorem. For the inverse
direction, apply reflection to the inverse rational Tate image and use the
actual rational linear isomorphism's inverse identity. The generic theorem
produces an actual abelian-scheme isomorphism `g` whose forward and inverse
arrows rationalize to the original arrows of `e`, with no integer multiples.
Injectivity of actual Hom rationalization transfers the original rational
equivariance equations to exact equivariance of both actual arrows for every
element of the original integral order. The supplied restrictions agree with
the unchanged rational actions, so this applies to those very restrictions.

`tateNormalizedCMIso_integral_polarization` shows that the actual lift has the
original scalar polarization equation as exact integral cross-multiple data.
Rationalizing the constructed integral dual pullback agrees with rational dual
pullback. Substituting the original rational forward arrow and its original
polarization equation, then using the existing exact integral-multiple
criterion, proves the claim with multiplier `q`. There is no denominator-square
factor because the actual arrow rationalizes to `e.hom` itself.

`TateNormalizedCMIntegralIsoRelated` retains `q`, `e`, the original geometric
polarization equation, an actual isomorphism with both rational agreements,
exact integral-order equivariance in both directions, the integral polarization
cross-multiple data with scalar `q`, and the exact original level equation.
`tateNormalizedCMRelated_iff_integralIsoRelated` proves this formulation
equivalent to the existing `TateNormalizedCMRelated` relation. Its forward
direction applies the two constructions above to the original witnesses; its
reverse direction forgets the added witnesses through the existing
polarized-multiple equivalence. The final theorem combines this equivalence with
the existing equality criterion for the original CM classes.

The provenance is internal: these are consequences of the existing carried
lattice, original level-isogeny, rationalization, integral polarization and
connected integral-reflection constructions. No new external theorem is
assumed. The lift requires neither lattice realization nor a representing
scheme. The comparison retains the source-stabilizer hypothesis and the
original scalar; it does not identify polarizations without that scalar or
establish division-case representability.
