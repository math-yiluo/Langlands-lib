# Descent of semilinear isomorphisms to supplied coefficient models

This internal construction descends an actual upstairs semilinear
isomorphism to an existing coefficient model. It uses domains R and A,
specified fraction fields K and L, the actual coefficient algebras and their
two scalar towers, and arbitrary common universe `u`.

Let N be an integral model over R of a K-group G. Its coefficient base change
to A is identified with a supplied model P by a compatible integral-model
isomorphism e extending a specified generic isomorphism η. Compatible integral
and field endomorphisms are supplied over both coefficient rings, with their
commuting squares. An actual isomorphism from the corresponding twist of P
to P is supplied, extending an upstairs generic isomorphism f'. A downstairs
generic isomorphism f from the twist of G to G is also specified.

`coefficientSemilinearIso` constructs the actual upstairs isomorphism between
the coefficient base change of the twist of N and that of N. It reverses the
coefficient/twist comparison, twists the recovery isomorphism e, applies the
supplied semilinear map, then reverses e. Its generic isomorphism is exactly
the corresponding composite, named `coefficientSemilinearGenericIso`.

The required generic compatibility equation says that the pullback of η
followed by f' equals the generic square comparison followed by the pullback
of f and then η. This equation identifies the generic map of the constructed
conjugate with the coefficient pullback of f; cancellation of the inverse
comparisons proves that equality in `coefficientSemilinearIsoOver`.

For `semilinearIsoFromCoefficients`, the integral coefficient map is assumed
flat and surjective. Quasi-compactness is available for these spectra. The
published `Iso.descendFromCoefficients` then descends the actual conjugate
isomorphism to `(N.twist ...).Iso N f`. Its Čech compatibility is automatic
from its prescribed original generic map. No additional compatibility of
integral Čech data is assumed.
`baseChange_semilinearIsoFromCoefficients` recovers the full supplied
conjugate isomorphism after coefficient pullback, and
`semilinearIsoFromCoefficients_generic_comm` proves the exact generic
semilinear law for the descended actual map.

The auxiliary `pullbackComparison_semilinear` proves the generic
compatibility equation for the canonical tower comparison and canonical
semilinear isomorphisms. Its proof compares projections to the original
group using the universal property of the actual pullback. The utility
constructors `Iso.trans`, `Iso.symm`, `Iso.changeGeneric`, `Hom.twist` and
`Iso.twist` retain exact generic compatibility under the required operations;
twisting uses naturality of the square comparison.

This is an internal derivation from actual model comparisons, square
naturality and automatic coefficient isomorphism descent. It assumes both
the downstairs model and its upstairs recovery, the upstairs semilinear
isomorphism, compatible endomorphisms and the displayed generic equation.
It constructs no finite field of definition, Galois automorphism lift,
arithmetic cover or upstairs extension and does not prove KP Fact 2.10.16.
