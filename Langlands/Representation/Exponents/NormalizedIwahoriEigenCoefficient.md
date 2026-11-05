# Exact coefficients for generalized normalized Jacquet exponents

Author: Worker 1680.

This internal supporting derivation connects the actual normalized Jacquet
quotient to ordinary compact-compression eigen-coefficients. It uses the
published localization, character twist, generalized character and compact
compression constructions. The compact-open Iwahori contractions for the
specified point remain explicit hypotheses. No structural existence theorem,
analytic square-integrability implication or whole Casselman criterion is
asserted.

`HasIwahoriContractionBasisAt` requires compact open Iwahori contraction
data for one fixed ambient element with arbitrarily small Levi
intersections. The existing `HasIwahoriContractionBasis` allows a different
element for each subgroup. The displayed implication forgets the fixed
element and proves that the new condition implies the existing condition.
It does not prove either condition for a reductive group.

`characterTwistedAction_mem_fixedVectors_of_mem_center` shows that a
scalar twist of a central Levi action preserves the subspace fixed by any
subgroup of the ordinary coinvariant action. Move a subgroup element past
the central action and use its fixed-vector equation; scalar
multiplication also preserves the subspace. `centralTwistedFixedAction`
is this actual restricted endomorphism.

`exists_jacquet_eigenvector_of_twisted_genEigenvector` begins with one
nonzero generalized eigenvector of a twisted central operator, lying in
the specified ordinary fixed-vector subspace. Mathlib's restriction law
for generalized eigenspaces puts it in the generalized eigenspace of
`centralTwistedFixedAction`. The theorem that a generalized eigenvalue
is an eigenvalue gives an ordinary eigenvector in that same subspace.
Multiplication by the inverse unit scalar removes the twist. The
ordinary eigenvalue is `η(z)⁻¹ μ`. This step needs no finite-dimensional
Jacquet module or common eigenvector for an entire torus.

`exists_eigen_coefficient_of_twisted_genEigenvector` then applies the
ordinary eigenvector lift and averaging construction from
`IwahoriEigenCoefficient`. For the given compact open subgroup it yields a
fixed vector and an invariant smooth functional nonzero on that vector,
with coefficient `ℓ(π(z^n)x) = (η(z)⁻¹ μ)^n ℓ(x)` for every natural
number `n`. Finite-dimensional source fixed vectors and the supplied
Iwahori contraction are used in that lift.

`normalizedJacquetOrdinaryEquiv` is the published localization equivalence
for the trivial radical character, twisted by the actual inverse-half
Haar-modulus character. It identifies the actual normalized functor's
representation with that character twist of ordinary coinvariants.
The application law is the actual quotient-projection formula.

Finally,
`exists_eigen_coefficient_of_normalizedJacquet_generalizedEigencharacter`
takes a generalized character of the actual normalized functor pulled
back along any supplied group homomorphism into the Levi. Its selected
point is assumed central in the Levi and to satisfy
`HasIwahoriContractionBasisAt`. Transport the generalized character through
the displayed equivalence and choose one nonzero generalized vector.
Smoothness of ordinary coinvariants gives an open Levi subgroup fixing
this vector. The supplied cofinal condition chooses a compact open
subgroup with a smaller Levi intersection and the required contraction
for that same point. Admissibility of the original representation gives
finite-dimensional source fixed vectors. The preceding theorem then
produces the exact coefficient, with eigenvalue the inverse of the
actual inverse-half modulus times the given character value.

The group, character-domain and representation carrier universes are
independent. The final theorem retains the actual normalized quotient,
closed radical, normalizing Levi and smooth admissible representation.
It assumes no global Jacquet admissibility, irreducibility or finite
length. The additional point-specific contraction basis is supplied
geometric data and has not been derived from the original hypotheses of
the represented-parabolic Casselman criterion.
