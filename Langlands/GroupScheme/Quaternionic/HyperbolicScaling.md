# Hyperbolic scaling by central units

This internal derived module defines the `D`-linear endomorphism that multiplies
the first hyperbolic coordinate by a unit `t` of `K`, the second by `t⁻¹`, and
fixes the orthogonal remainder. The two polar coordinates transform by these
respective scalars, and the remainder is fixed. These formulas give the identity
and multiplication laws and preservation of the complete quotient-valued
quadratic form.

The calculation of the quadratic value uses the decomposition proved in
`HyperbolicDecomposition`. Its plane term changes from `[a σ(b)]` to
`[(t a) σ(t⁻¹ b)]`; the involution fixes `K`, so the central units cancel.
The scaling maps are packaged as a homomorphism into the unit group of the
endomorphism ring. Its action on the first nonzero singular vector makes this
homomorphism injective. This is a linear-algebra construction, preceding construction
of a group-scheme morphism; no split-rank conclusion is asserted here.
