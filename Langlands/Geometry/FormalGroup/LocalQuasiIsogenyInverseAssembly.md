# Local inverse assembly from integral scalar-power duals

This module connects integral scalar-power dual isogenies to the
published `LocalQuasiIsogenyInverseStatement`. It retains the statement's
arbitrary commutative coefficient ring O, commutative O-algebra R,
O-algebra field F, independent universe for O, and finite coordinate
types. It adds no domain or fraction-field condition.

`RationalSection.ofIntegral_smul` identifies the integral image of a
scalar multiple with multiplication of the section by the scalar's
image in F. Applied to the actual scalar endomorphism, this identifies
its integral section with the appropriate scalar multiple of the
actual identity section.

`RationalSection.IsLocallyScalarIsogeny.inv_pow_smul_ofIntegral` verifies
that the inverse of a power of the nonzero scalar image, times the
integral section of an actual isogeny, has the local scalar-isogeny
property. Its witness uses the same open set, integral isogeny and
denominator exponent.

`RationalSectionIso.exists_locallyScalar_of_integralDual` starts with
an actual forward section z satisfying c^n z = f, where c is the image
of pi in F. It assumes an actual reverse integral isogeny g such that
both integral composites are the scalar endomorphism pi^(n+k).
The constructed reverse section is (c^k)^(-1) times the integral image
of g. Bilinearity of section composition, the integral composite
identities, and cancellation of the nonzero scalar powers prove both
actual inverse equations. The preceding denominator lemma proves the
reverse local isogeny property.

`localQuasiIsogenyInverse_of_integralDuals` proves the complete published
target conditional on an eventual scalar-power dual theorem for
integral isogenies over the actual ring of sections of each open set.
That premise says that between the scalar-divisible formal modules
there is a reverse integral isogeny with both composites pi^j for
every sufficiently large j. The scalar-divisibility conditions needed
in the premise follow by the existing arbitrary coefficient extension
theorem from those retained by the input local quasi-isogeny.

At each point, choose a neighbourhood and denominator exponent n
from the input local condition. Choose j to be the maximum of n and
the dual theorem's threshold, and set k = j-n. The scalar computation
above supplies a local actual inverse with the reverse local isogeny
property. The actual inverse-section gluing theorem gives the unique
global inverse with the same forward section. Every choice of
neighbourhood and denominator may depend on the point.

This module does not prove the eventual integral scalar-power dual
premise. In particular it does not claim an unconditional proof of
`LocalQuasiIsogenyInverseStatement` or invoke the general finite-kernel
composition theorem (proved in the Library as
`Hom.finiteKernelCompositionStatement` in `FiniteKernelComposition`).
The provenance is the internal algebraic and sheaf assembly of the
published target, rather than a quotation from external literature.
