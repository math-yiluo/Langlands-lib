# Original ambient Haar ratio for the represented compact comparison

This internal adapter identifies the Haar character in the existing natural
compact-comparison family for the original represented orbit stabilizer.
It uses the original target Levi projection and its original section.
The section identifies the compact inducing subgroup with the literal full
target intersection, preserving each ambient rational point and its topology.

The implementation proves that the original stabilizer is the ambient
intersection with the inverse-conjugate source parabolic. Equality transports
the published `splitStagesAmbientHaarRatio_apply` theorem to the original
stabilizer type, including its actual nested kernel and intersection.
The resulting complex character is exactly the original target-radical
modulus divided by the modulus of the literal target-radical intersection
with that conjugate source parabolic.

The two original positive moduli have open kernels by the existing
closed-normalizer modulus theorem. Their common kernel is contained in the
kernel of the resulting complex ratio, proving that its scalar twist
preserves smooth coefficients.

All measurable spaces in the represented specialization are the Borel spaces
used by `representedCompactComparisonFamily`; local compactness of its nested
kernel comes from the original represented radical. The adapter introduces no
Haar equality as a hypothesis, and it does not require a dynamic realization.
It does not identify the coefficient quotient action, cancel the normalization
characters, construct a final functor isomorphism, or prove the closed local
orbit-comparison proposition.

The provenance is internal: the subgroup and continuous-equivalence arguments
are derived directly from the existing represented compact-comparison
construction, and the Haar calculation specializes the already implemented
ambient split-stages calculation. No new literature assertion is used.
