# Compactly supported profiles of regular orbital integrals

This internal construction implements the compact-open test function argument of
Henniart–Lemaire (2011), I.2.7, Lemma 2, for a supplied family of compatible
quotient measures. The hypotheses specify an open invariant regular locus, a
continuous open map to a Hausdorff space of orbit parameters, and integrability,
local constancy and invariance of the actual Library orbital integrals.

`RegularOrbitalProfileData.exists_profile` descends each orbital integral
function to the parameter space. The image of the support of the test function
in that space is compact. Any orbit with parameter outside that image sees the
zero function. The open parameter map gives local constancy on its image, and
the complement of the compact support image gives local constancy at the
other parameters.

`RegularOrbitalProfileData.exists_test` proves the converse. Compactness and
openness of the parameter map give one compact open cutoff in the regular
locus that meets orbits over the support of a desired profile. The orbital
integral of its characteristic function there is the mass of a nonempty
open subset of the actual quotient. Compatibility gives positivity and the
integrability hypothesis gives finiteness. On the cutoff, the constructed
test function is the desired profile divided by the profile of the cutoff,
evaluated at the orbit parameter. Its extension by zero is locally constant
and compactly supported. The ratio is constant on the orbit, so it factors
out of the quotient integral. Multiplication by the cutoff integral recovers
the desired profile.
