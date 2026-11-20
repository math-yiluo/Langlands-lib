# Assembling the normalized packet from its weak and positive terms

`RationalOrbitLevelWeakPacketRapid` is the estimate on the weighted weak
integral needed from the lower-Levi packet argument. It includes Bochner
integrability and controls the integral times the standard half modulus
by ambient Xi, the full matrix height and finitely many original section
seminorms. `RationalOrbitLevelProperPacketRapid` gives the corresponding
estimate on the original packet on the intersection of the threshold and
positive regions of the selected standard parabolic.

`rationalOrbitLevelProperPacketRapid_of_weak_positive` uses the actual
fixed-level threshold identity and the weak-plus-positive decomposition
of the normalized constant term. The weighted weak term is integrable
by the weak estimate. On the threshold region, subtracting this term
from the integrable original coefficient proves integrability of the
weighted positive term. The uniform full-height positive estimate then
bounds its integral by the same seminorm weight times the integral of
the norm of the original density. The triangle inequality and the
union of the finite sets of seminorms give the original packet bound.

This derived step of Waldspurger VI.3.1 uses the original weight and orbit
measure throughout. The weak estimate is its remaining lower-rank input.
