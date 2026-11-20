# Scalar meromorphic uniqueness

This module derives the scalar identity principle for the local denominator
predicate of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, §3.1. The continuous linear identity map on `ℂ` converts scalar weak
holomorphy to complex Fréchet differentiability. On a convex open set the proof
restricts a function to a complex affine line through a point of its open zero
set and an arbitrary test point. The parameter domain of the line is convex
as a real set. The one-variable identity theorem then gives equality at the
test point. Open balls and connectedness extend the argument to connected open
sets.

For a meromorphic function, consider the open set on which it vanishes locally
wherever it is holomorphic. At a limit point choose a local denominator and
numerator. The numerator vanishes on the intersection of the neighborhood
with the open set by density and continuity. The holomorphic identity theorem
forces it to vanish throughout the neighborhood. The denominator cannot vanish
on any nonempty open subset there. Continuity of the meromorphic function on
its holomorphy domain then forces it to vanish on that whole part of the
neighborhood. This proves the locally vanishing set is closed, so connectedness
extends any initial open vanishing to the entire holomorphy domain.

For arithmetic, take a ball around the point within both local presentation
neighborhoods. The holomorphic identity theorem implies that the first
denominator has a nonempty open nonvanishing locus on this ball. The second
denominator is nonzero somewhere on that locus. The product denominator
therefore works for both addition and multiplication. If the presentations
are `d f = n` and `e g = m`, the new numerators are `e n + d m` for the
sum and `n m` for the product. Negation keeps the denominator and
negates the numerator. A constant has denominator one. Induction using
addition gives meromorphy of finite sums on a common open dense domain.
Applying the vanishing principle to the difference gives equality on the
whole common domain of two scalar meromorphic functions that agree on
its intersection with a nonempty open set.

The coordinate lemmas apply these operations in each chart. Pullback by a
linear equivalence composes every chart with that equivalence. Equality in
one chart suffices for the identity principle because its inverse supplies
a coordinate for every point of the parameter space.
