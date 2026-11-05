# Exact Haar expressions for corrected-orbit cocharacters

This internal construction and deduction by Worker 561 connects the
actual cocharacter realization with the exact Haar expressions in
`RationalCorrectedOrbitSquaredModulusStatement`.

For a `CorrectedOrbitCocharacterRealization r`, `actingScheme` is the
published affine representative of the first dynamic centralizer and
`actingHom` is its original inclusion into the ambient group.
Its image centralizes both cocharacters by `r.centralizer_eq`.
`leviPointEquiv` identifies its rational points with the original
`levi i ν I` by the represented-subgroup `pointsEquiv` and
`MulEquiv.subgroupCongr`; this equivalence preserves the original
ambient values. Thus it covers every Levi point.

The closedness lemmas use the two given closed standard radicals and
the literal subgroup equalities of the realization. The right radical
is a preimage under continuous inverse conjugation. The intersection
uses `CorrectedFiltration.isClosed_orbitUnipotentIntersection`.

`haar_left`, `haar_right` and `haar_intersection` compare the three
published centralizing Haar characters with the exact three
`HaarModulus.closedRestrictCharacter` values of the target.
The first and third comparisons identify the literal closed subgroups
and their normalizer elements by their ambient values. The second
uses `closedNormalizerCharacter_conj` and evaluates the original
second radical at the exact `conjugationEquiv m hK` of the Levi point.
The normalizer witnesses are the given semidirect decompositions'
`levi_le_normalizer` and the published
`CorrectedFiltration.levi_le_normalizer_orbitUnipotentIntersection`.
All comparisons use the forward Haar convention and hold as equalities
of positive units.

`squared_modulus_of_dynamic_balance` specializes a full acting-group
three-factor Haar identity at the inverse image of any original Levi
point and rewrites those three comparisons. Its balance hypothesis
is explicit: this lemma does not prove that balance or the whole
unapplied rational target and does not discharge character restriction
injectivity. No structural premise is added to the target itself.
The field has arbitrary universe, and the affine ambient group and torus
are those of the realization. The Haar comparisons use the canonical point
topology, local compactness and the displayed nonarchimedean point-group
hypothesis. No Hausdorff or local-field hypothesis is required here.
