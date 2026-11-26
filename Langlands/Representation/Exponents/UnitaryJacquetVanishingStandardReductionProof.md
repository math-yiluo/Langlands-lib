# Proof of standard testing of unitary Jacquet vanishing

`Langlands.Aubert.General.RepresentedParabolic.unitaryJacquetVanishingStandardReduction`
proves `UnitaryJacquetVanishingStandardReductionStatement` for smooth complex
representations, with independent field and representation-carrier universes.

Vanishing at every proper rational parabolic applies to each proper pair in
the fixed standard family. For the reverse implication,
`DynamicLeviConjugacy.exists_cocharacter_parabolic_levi` realizes the specified
parabolic and Levi as the dynamic parabolic and centralizer of one cocharacter,
using `parabolicDynamic` and `dynamicGeometricUnipotentRadical`. By
`exists_simultaneousStandardConjugate_of_dynamicRealization`, maximal split
torus conjugacy and the relative root system give a rational point \(g\) whose
inner automorphism carries both subgroup images to the standard pair for a
subset of the simple roots.

The proof postcomposes the parabolic inclusion \(p\) with that automorphism and
keeps the Levi, radical and split-component maps. Composition with
an isomorphism preserves properness by `isIso_comp_right_iff`. The standard
test therefore gives zero unitary part for the conjugated inclusion.

By `unitaryJacquetPart_eq_bot_iff`, every normalized exponent for that inclusion
has nonzero normalized real part. The lemma
`isNormalizedJacquetExponent_comp_innerIso_iff` carries each original
normalized exponent to the conjugated inclusion with the same character of
the same split component. The real part depends on that character and split
component, so it is nonzero for every original exponent. A second application
of `unitaryJacquetPart_eq_bot_iff` gives the required vanishing.

This is the conjugation comparison for the vanishing condition in David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, VII.2.4, Lemma, printed p. 230 (PDF p. 236). The standard family
and rational parabolic conjugacy are described in V.3.8–9, printed pp. 111–112
(PDF pp. 117–118), and the unitary part is defined in VII.2.3, printed p. 229
(PDF p. 235). The source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
