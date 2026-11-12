# Bernstein data and represented supercuspidality

This derived adapter compares the two actual cuspidality interfaces used in
the Bernstein support argument.
`BernsteinCuspidalDatum.isSupercuspidal` proves that every published
`BernsteinCuspidalDatum` has vanishing normalized Jacquet module for every
proper actual represented parabolic of its actual rational Levi. It retains
the arbitrary nonarchimedean local field, actual `BernsteinStandardFamily`,
canonical rational-point topology and independent field and carrier
universes. It adds no representation-theoretic or structural premise.
The entry construction `BernsteinCuspidalDatum.representedSupercuspidal`
returns the original representation together with its irreducibility and
this all-actual-parabolic supercuspidality certificate. Its underlying
representation is definitionally the datum's original action.

`bernsteinStandardRepresentativesGeometric` applies the published standard
cocharacter theorem and the geometric recognition of standard representatives.
It supplies parabolicity, the rational Levi property, the geometric radical
property and the multiplication isomorphism for the original choice-free
standard schemes. In particular the actual Levi is connected reductive.

For the main theorem, the ambient maximal split torus factors through this
Levi and is still maximal split. The published exact standard-family
comparison supplies genericity of the same cocharacter inside the Levi.
Relative roots supply a finite set of intrinsic simple roots. The actual
Levi points inherit local compactness and the nonarchimedean group property
through the canonical homeomorphism with the closed literal Levi subgroup.
Hausdorffness of the field follows from the published local-field topology
theorem; it is not an additional assumption.

`rationalLeviCuspidalityTransport` identifies the datum's inside-Levi Jacquet
tests with the Levi scheme's own proper standard tests, after pulling back
along the canonical rational-point homeomorphism. The pullback round trip
is isomorphic to the original representation, so the latter is cuspidal
for this intrinsic standard family. The represented cuspidality comparison
then tests every proper actual parabolic, with every supplied rational Levi
and geometric radical preserved. Published proofs discharge dynamic
parabolic recognition, maximal split-torus conjugacy, relative roots,
standard cocharacters and the dynamic Lie comparison.

The source motivation is Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, VI.2.1 Remark 1, printed p.137 /
PDF p.143, and VI.5.4, printed pp.173–174 / PDF pp.179–180, used in
VI.7.1–VI.7.2. Those original passages were read. Source ID:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This is an internal comparison of existing definitions, not a proof of
cuspidal-support association or the Bernstein decomposition.
