# Spreading local surjectivity over a unique prime

This internally derived helper concerns a finite algebra S over a commutative
ring R and primes q of S and p of R. The hypothesis states that q is the only
prime of S above p. If the actual induced local homomorphism R_p to S_q is
surjective, there is r outside p such that the map R[1/r'] to S[1/r'] is
surjective for every multiple r' of r. Here S[1/r'] inverts the image of r'.
No Noetherian hypothesis, kernel finite-generation hypothesis, or unramifiedness
hypothesis is imposed. The rings may occupy independent universes.

The implemented proof adapts the surjectivity half of Mathlib's
Localization.exists_awayMap_bijective_of_localRingHom_bijective from the pinned
RingTheory/Unramified/LocalRing.lean. Surjectivity in localizations provides
numerators and denominators for each element. Uniqueness of the prime allows
clearing a denominator in S by one from R outside p. Choose finite algebra
generators and multiply the finitely many resulting denominators. Their images
then lie in the range after inverting a multiple of this product. The range is
a subalgebra containing the generators, hence contains all of S. Inverting the
base element also supplies the denominators of all fractions, giving full
surjectivity. The separate injectivity argument in Mathlib is unused.

PrincipalSurjectivityNeighborhood records the element, its exclusion from p,
and the surjectivity property for all multiples as data. The noncomputable
constructor principalSurjectivityNeighborhood chooses this data from the proved
existence result; it introduces no additional assumption or uniqueness claim.
The element can be used directly as the defining section of a scheme's basic
open neighborhood.
