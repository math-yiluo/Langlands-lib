# Nonzero ideal sheaves and smaller support quotients

`IntegralIdealOpenStatement` is an internal geometric prerequisite for comparing
an ideal sheaf with the structure sheaf in the Euler leading term.

Its first clause applies to every reduced scheme and every nonzero module
sheaf `I` equipped with an actual monomorphism into the structure module.
It asserts existence of a nonempty open on which that monomorphism becomes
an isomorphism. No finite type or quasi-coherence hypothesis is required:
some local section has a nonzero scalar image, whose basic open is nonempty
by reducedness. On that basic open the image contains a unit, so the
monomorphism is also an epimorphism.

The second clause assumes the scheme is integral and its actual topological
Krull dimension is at most a natural number `d`. The actual categorical
cokernel of the same monomorphism then has `HasSupportDimensionLT` bound
`d`. Indeed, it vanishes on the nonempty open from the first clause.
Irreducibility makes the closed complement have strictly smaller support
height. This clause includes dimension zero, where the cokernel is zero.

Both clauses use the existing actual module sheaves, restriction functors,
structure module, categorical cokernels and closed support-height predicate.
They do not assert a filtration or Euler polynomial, and do not assume the
ideal is an invertible module. The rationale is an internal derivation from
local scalar images, reducedness and the published smaller-support lemmas;
it is not a translation of an external numbered theorem.
