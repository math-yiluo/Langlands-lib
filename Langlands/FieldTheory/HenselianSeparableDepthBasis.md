# Integral and rational bases for actual separable depth lattices

For a surjective integer valuation on a field `K` with Henselian valuation
ring `O`, and a finite separable extension `L/K`, the actual real-depth ball
is a finite free `O`-module. Inverting the nonzero elements of `O` in its
inclusion into `L` gives all of `L`: each element of `L` can be moved into
the ball by a nonzero integral scalar. Injectivity of the inclusion supplies
the remaining equality condition for module localization.

Choose an integral basis of this ball. Module localization promotes its
vectors to a `K`-basis of `L`, so the number of integral basis vectors equals
the field degree. Reindexing gives `henselianSeparableDepthIntegralBasis`
and `henselianSeparableDepthFieldBasis`, both indexed by that degree.
The field-basis coordinate of an integral vector is the image of its
integral-basis coordinate. Its integral span is exactly the actual depth
ball. An element belongs to the ball if and only if all of its field-basis
coordinates belong to `O`; the reverse implication expands it in the basis.

These are internal linear algebra constructions supporting the additive
models in Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Section C.2, printed pp.697–698 (PDF pp.728–729). The basis choices and
localization argument are derived here. No group-scheme model, supplied
root identification, apartment comparison, or complete C.5.3 claim is made.
