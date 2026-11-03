# Modular characters in continuous semidirect coordinates

Author: Worker 53.

This internal development compares Mathlib's modular character with the Haar
modulus of inner conjugation and then computes it in the published continuous
semidirect coordinates. It is supporting material for the exact rational
parabolic modulus proof; it does not establish reductive unimodularity.

`innerConjugation g` is the continuous multiplicative equivalence sending
`x` to `g * x * g⁻¹`. For every locally compact topological group,
`modularCharacter_eq_innerConjugation` identifies its Haar modulus with
Mathlib's modular character at `g`. Left invariance identifies pushforward by
inverse conjugation with pushforward by right translation. The existing
`mulEquivHaarChar_smul_eq_comap` and `modularCharacterFun_eq_haarScalarFactor`
then give the equality, with the same orientation as the Library's
`HaarModulus.normalizerCharacter`. This result has no countability premise.

The remaining results concern actual subgroups `P`, `M`, `U` of a second
countable topological group, with `IsSemidirectDecomposition P M U`, continuous
Levi projection, and locally compact `P`, `M`, `U`. All subgroup measurable
spaces are their Borel spaces. Second countability supplies the product Borel
and Haar regularity properties used by the product measure argument.

`modularCharacter_unipotent` proves that the modular character of `P`
restricted to `U` is the intrinsic modular character of `U`. Right translation
by `u` acts on Levi-then-radical coordinates as `(m,v) ↦ (m,v*u)`.
The product Haar measure therefore scales by the intrinsic modular character
of `u`; pushing through the coordinate homeomorphism and taking
`haarScalarFactor` proves the assertion.

`modularCharacter_levi` proves that the modular character of `P` at a Levi
element is the product of the intrinsic Levi modular character and the Haar
modulus of its conjugation on `U`. Inner conjugation by the Levi element
preserves both factors, so the published `haarChar_eq_mul` applies.

`modularCharacter_eq_restrictCharacter` extends equality on the two factors
to `P` by writing `p = m*u` and using multiplicativity. Its hypotheses are
Levi unimodularity, triviality of the ambient modular character on `U`, and
triviality of the radical's inner normalizer character.
`modularCharacter_eq_restrictCharacter_of_unimodular` removes the separate
ambient-radical premise using `modularCharacter_unipotent` and the
inner-conjugation comparison. Its only unimodularity inputs are the intrinsic
Levi character and the radical's inner normalizer character.

The actual rational-point application in `RationalParabolicModulusReduction`
derives second countability using `RationalPointSecondCountable` and uses the
published standard-unipotent unimodularity proof. It retains actual
standard-Levi unimodularity as a premise. This supporting material does not
prove the full rational-parabolic modulus target.

`innerConjugation` reuses the published continuous multiplicative equivalence
`Langlands.Continuous.innerConjugationEquiv`, with forward map
`x ↦ g * x * g⁻¹` and inverse `x ↦ g⁻¹ * x * g`.
