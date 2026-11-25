# Standard testing of unitary Jacquet vanishing

`Langlands.Aubert.General.RepresentedParabolic.UnitaryJacquetVanishingStandardReductionStatement`
compares the vanishing condition of Renard VII.2.4 with its represented-parabolic
form in `TemperedSquareIntegrableUnitaryPartStatement`. The source tests the
unitary Jacquet part at proper standard parabolics. The represented form tests
it at every proper rational parabolic. This comparison isolates the conjugation
argument, which applies to any smooth complex representation.

Fix a Hausdorff nonarchimedean local field and a connected reductive group scheme
`G`. With the rational-point topology, assume that `G(k)` is locally compact and
nonarchimedean. A maximal split torus `i` and a generic cocharacter `ν` fix the
standard family. The field and representation-carrier universes are independent.

For a smooth complex representation `π`, the left side asks that the subrepresentation
`unitaryJacquetPart p l r hp hl hr hmul ha π` be zero whenever `p` is a proper
rational parabolic. It quantifies over the represented parabolic, its rational
Levi, geometric unipotent radical with the Levi decomposition isomorphism, and
the split component of the Levi. The right side imposes the same condition on
the represented pairs whose images as subgroup functors are `standardParabolic i ν J`
and `standardLevi i ν J`, where `J` ranges over subsets of `simpleRelativeRoots i ν`.
Both sides express properness by `¬ IsIso p`. The comparison requires only
smoothness of `π`. Admissibility, temperedness, a central character and a quotient
Haar measure enter the separate square-integrability criterion.

This derived proposition uses the actual standard families of V.3.8–9 and the
unitary part of the normalized Jacquet module defined in VII.2.3. Its vanishing
condition is the one in the lemma of VII.2.4. The source is David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026,
printed pp. 111–112 and 229–230 (PDF pp. 117–118 and 235–236), registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
