# Unitary central character of a selected unitary Jacquet quotient

This derived supporting construction concerns the irreducible quotient selected
in Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026,
VII.2.6, first proof paragraph, printed p.231 / PDF p.237. The registered source
is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source applies VII.2.4 to that quotient. This unit provides its unitary
central-character input, conditional on the separately stated structural
compactness of the full scheme center modulo the actual split component.
It does not apply VII.2.4 or assert that compactness.

The hypotheses retain the Hausdorff nonarchimedean local field, connected
reductive ambient group, canonical rational-point topology, supplied locally
compact and nonarchimedean group instances, and every actual parabolic, Levi,
matching geometric radical, multiplication isomorphism and split component.
The field universe `u` and representation carrier universe `v` are independent.
The input `D` is the actual irreducible smooth quotient of the unitary Jacquet
summand, together with its actual surjective quotient map. Its existence is not
asserted here. The two split-component lemmas use an affine-Levi instance and
the canonical topology; the final construction derives that affine instance
from the rational Levi witness and installs the published `leviPointTopology`.

`splitComponentCentralCharacter_realPart_eq_zero` applies to any full-center
scalar character of `D.quotient`. Source temperedness supplies the complementary
unitary/nonunitary Jacquet splitting. The proof extends the quotient map to the
full normalized Jacquet module by the corresponding retraction and transports
it back to the literal Levi image with the same underlying linear map.
The target split-component action is scalar with the restricted character.
A nonzero image of a source generalized weight therefore forces equality of
the weight character and the restricted scalar character: an eigenvector can
belong to a generalized eigenspace only for its own eigenvalue. If the
restricted character had nonzero normalized real part, this map would kill
every source weight with zero normalized real part. The supremum description
of the unitary part then shows that its restriction to the whole unitary
summand is zero. That restriction is the given surjective quotient map, which
contradicts the nonzero irreducible target. Thus the restricted scalar
character has zero normalized real part. No temperedness of the unitary
Jacquet summand or its quotient is used.

`splitComponentCentralCharacter_norm_eq_one` derives an open kernel for the
restricted scalar character directly from the smooth nonzero quotient and
the continuous actual split-component point map. The published split-torus
norm formula then turns zero normalized real part into unit modulus at every
actual split-component point.

`UnitaryJacquetIrreducibleQuotientData.unitaryCentralCharacter` constructs an
actual `UnitaryCentralCharacter` for `D.quotient`. It uses the scalar character
already constructed from admissibility in `TemperedUnitaryQuotientStructure`,
the split-component norm theorem above, and the published
`unitaryCentralCharacterOfSplitComponent` construction. The resulting datum
contains that full-center multiplicative character, its open kernel, its
norm-one proof at every center point, and its scalar action. The explicit
input `CenterSplitComponentCompactness M hl.isConnectedReductive A a ha`
concerns the actual full scheme-center quotient with its inherited quotient
topology. The extension theorem uses rational-center comparison and compact
quotient unitarity to obtain norm one on the full abstract point-group center.

This is an internal derivation from the actual unitary Jacquet quotient,
central weight spaces, smooth-character norm formula and full-center extension
construction. It does not prove the structural center compactness input,
unitary Jacquet temperedness, quotient temperedness, nested transitivity,
square-integrability, or any of the three final VII.2.6 propositions. The final
VII.2.6 statements retain their original hypotheses; this supporting
construction does not discharge any of them.
