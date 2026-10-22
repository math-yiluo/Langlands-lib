# Convolution law for the integrated action

The actual finite-fiber action satisfies
`π(f * g)v = π(f)(π(g)v)` for the convolution constructed in
`Hecke.TestFunction.convolution`. The measure is left invariant and finite on
compact sets, and the measurable structure is the Borel structure of the
topological group. The smooth complex representation remains in an independent
universe, with no topology, norm or completeness assumed on its vector space.

The proof tests the vector equality against every algebraic complex linear
functional. Algebraic dual separation reduces the claim to scalar integrals
using `integratedAction_dual`. The double scalar kernel is continuous because
the smooth orbit coefficient is locally constant. Its support lies in the
compact product `(support f * support g) × support f`, regardless of the support
of the orbit coefficient. Compact-support Fubini exchanges the two integrals
without a global sigma-finiteness assumption. Left-Haar substitution `z = y w`
and the representation multiplication law give the iterated action.

The resulting `heckeAction` is a complex nonunital algebra homomorphism from the
actual measure-indexed `HeckeAlgebra μ` to the endomorphisms of the vector space.
Its multiplication law is the integral theorem above. Left translation of the
test function corresponds to the positive group action on the output, by
measure-preserving change of variables and naturality of the algebraic integral.
Consequently, left subgroup invariance puts the image into the existing
fixed-vector submodule. An unnormalized compact-open indicator acts on a fixed
vector by the Haar mass of its subgroup; this uses the finite-fiber integral of
a constant indicator.

This is an internal proof of the natural Hecke action described by Flath,
section 1, printed page 179, registered as `flath-1979-tensor-products`.
The finite-fiber construction is original project implementation.
The integral, integrand and genuine convolution algebra are imported from the
published Library. This progressive unit does not yet construct normalized
fixed-vector projections, unital corner modules or local units; those remain
subsequent obligations of the task.
