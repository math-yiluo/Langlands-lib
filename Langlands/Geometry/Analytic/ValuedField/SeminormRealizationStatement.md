# Complete-field realization of an ultrametric multiplicative seminorm

`Langlands.Analytic.SeminormRealizationStatement` asserts that, for every
commutative ring `A : Type u` and every nonarchimedean multiplicative ring
seminorm `q` on `A`, there are a complete ultrametric normed field
`L : Type u` and a unital ring homomorphism `f : A →+* L` such that
`‖f a‖ = q a` for every `a`.

Mathlib's `MulRingSeminorm` includes normalization at one, multiplicativity,
nonnegativity, the ordinary triangle inequality and invariance under negation.
The additional `IsNonarchimedean q` hypothesis is the strong triangle
inequality. The source ring has no prescribed topology or norm and need not
be a domain or reduced. The map may have a kernel; the exact norm identity
identifies it with the zero set of `q`. Normalization excludes a seminorm of
this kind on the zero ring without imposing a separate nonzero hypothesis.
All universes, including `u = 0`, are allowed.

This internal auxiliary interface isolates the residue-field realization
step in the common-field proof for compatible affinoid points. The intended
construction takes the quotient by the seminorm kernel, its fraction field
with the induced absolute value, and its metric completion. It generalizes
the published spectrum-point construction in
`Langlands.Geometry.Analytic.Spectrum.ResidueField.Definitions` to a ring
with a supplied multiplicative seminorm. This file states the interface;
it does not assert a proof of field amalgamation or of the required tensor
seminorm construction.
