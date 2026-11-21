# Density from opposite continuations for a square-integrable representation

`DensityPackage.ofSquareIntegrable` takes the two actual full-domain
opposite continuations and their nonempty open convergence subsets at a
compact with both parabolic products. It retains that compact and those
continuations in the resulting density package.

The ambient group is connected reductive over the given nonarchimedean
local field. The inducing representation is irreducible and square
integrable modulo the point image of a split component of the dynamic
Levi. The proof specializes the published
`DynamicCommonLeviIrreducibility.hasOpenIrreducibilityLocus` to the source
parabolic to select the nonempty open locus. It obtains the finite
quotient by the norm kernel and split center from the Levi scheme's finite
split valuation index, via the actual multiplicative homeomorphism from
the scheme to its point subgroup. The quotient Haar and the supplied
square-integrability proof
are the ones used by `conditionalDynamicOppositeUnitaryScalar`, whose
regularity conclusion gives the inverse scalar value at every unitary
parameter. The field and representation carrier have independent
universes.

This derived construction is used for the lower density packages in the
rank induction of Waldspurger VI.3.1. The full-domain continuations remain
explicit inputs to the construction.
