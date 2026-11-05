# Rational characters and compactness of anisotropic tori

This is an internal prerequisite for the spectral route to compactness of
anisotropic connected reductive groups. Its torus result does not prove the
general reductive-group spectral integrality target or the full compactness
and anisotropy equivalence.

`AnisotropicTorusCompactnessStatement` states, at arbitrary universe `u`, that
every actual affine torus locally of finite type over an actual nonarchimedean
local field has compact rational points if it is anisotropic. The topology is
exactly `rationalPointTopology F T.X`, with affineness derived from the stated
affine structure map. The statement imposes no restriction on characteristic
or torus rank. Anisotropy means the imported split-rank-zero condition.

The supporting lemmas implement the following derivation. A closed subgroup of
an anisotropic group is anisotropic, because every closed split torus in the
subgroup composes to a closed split torus in the ambient group. For an affine
torus locally of finite type, a largest split subtorus exists and restriction
of rational characters to it is injective. In the anisotropic case its
character group is subsingleton, so every rational character of the torus is
zero. Consequently every rational character of a closed torus in an
anisotropic group takes the value one at every rational point. These results
hold over arbitrary fields, without local-field assumptions.

For any finite field extension, the imported `normCharacter` of a character of
the extended torus is a rational character of the original torus. The imported
`normCharacter_eval` identifies its value with the field norm of the extended
character value. Character triviality therefore makes that field norm equal
to one. This lemma requires neither separability nor a valuation on the
extension, and asserts a field-norm equality, without asserting that an
extension-character value is itself one.

For a local-field torus, triviality of every rational character identifies its
common normalized rational-character norm kernel with its entire rational
point set. The implemented compactness lemma then applies the published
`Langlands.Plancherel.torusNormKernelCompactness`. This is a direct reduction to
the existing torus norm-kernel proof; it uses no compactness theorem for a
general anisotropic reductive group. Affine and locally finite type hypotheses
on the torus are explicit, including when the torus is presented as a closed
subgroup of a larger group.

The provenance is derived from the imported Library results
`isAnisotropic_iff`, `IsAnisotropic.subsingleton_character`,
`exists_largestSplitSubtorus`,
`IsLargestSplitSubtorus.characterRestrict_injective`,
`TorusNormKernel.normCharacter_eval`, and
`Langlands.Plancherel.torusNormKernelCompactness`. The torus-character step is
compatible with the character argument in Kaletha-Prasad, *Bruhat-Tits theory:
a new approach* (2023), proof of Theorem 2.2.9, printed p.73 / PDF p.104. This
module does not construct group-point semisimple replacements or maximal tori,
and does not supply a comparison of arbitrary representation eigenvalues with
torus characters.
