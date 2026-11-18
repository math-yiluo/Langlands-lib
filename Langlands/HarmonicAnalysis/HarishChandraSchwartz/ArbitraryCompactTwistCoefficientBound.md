# Original twisted coefficients with an arbitrary source Levi compact

This derived module adapts the published `InducedCoefficientTwistXi` proof to
the arbitrary-source compact integral comparison. The ambient compact picture,
`twistedSection`, `CompactInduction.coefficientMap`, normalized ambient compact
Haar measure and ambient spherical function are exactly the original ones.
The source Levi spherical function may use any displayed compact open subgroup
`KM` with `M = (P₀ ∩ M) KM`. The minimal Levi character is assumed trivial on
its intersection with `KM`. No source factorization at `K ∩ M` is required.

`norm_twist_coefficientMap_le_xi_arbitraryCompact` fixes a section of the
original product compact picture and proves one positive bound for all
unitary unramified twists and all ambient group points. The representation
coefficient bound relative to the displayed `KM` spherical function remains
a hypothesis. Other premises are the published compact-picture construction's
closedness, continuity, compactness, admissibility and modulus hypotheses,
and the compatible `LeviData`.

The proof reuses `integrand_twist_bound` without changing its original
section transport. It takes the original chosen parabolic factorization,
reads its norm estimate as the arbitrary-compact Levi weight, and writes the
same original coefficient map as `compactIntegral`. The parabolic modulus is
trivial on `KM`: its open kernel and compactness imply this through the
published `eq_one_of_isOpen_ker_of_isCompact`. Finally
`LeviData.norm_compactIntegral_le_xi_arbitraryCompact` gives the bound with
the additional positive comparison factor. The source compact is never
identified with the original `K ∩ M`.

`norm_family_coefficientMap_le_xi_arbitraryCompact` treats a finite smooth
family in that same compact picture. Its finite smooth expansion supplies
finitely many fixed sections, each controlled by the preceding theorem.
Smooth scalar functions on the compact parameter torus are bounded. Linearity,
the triangle inequality and a finite sum give one positive constant before
all unitary characters and ambient points.

`arbitraryCompactFamilyXiConstant` selects such a constant, and its
specification states its positivity and the bound for the original
coefficients. The group, representation, character-index and torus-index
universes remain independent.

The module introduces no original-literature assertion. It is an internal
extension of the published twist/family argument using the newly proved
compact integral comparison. It retains the source representation coefficient
bound, the displayed source Iwasawa subgroup and its minimal-modulus premise.
It does not by itself discharge these hypotheses on actual rational points,
prove full packet derivative estimates, or prove the exact Schwartz target.
