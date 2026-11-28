# Comparison with the standard torus filtration

`minimalCongruentWeaklyInduced` proves equality with the standard
filtration at every nonnegative depth for a weakly induced torus over
`inertiaFixedField F`.

For an induced torus, `localTorusFiltration_eq_geometric_of_induced`
identifies positive standard terms with the geometric character
subgroups. At shallow positive depth, the identity map puts this
subgroup in the minimal congruent term. For the other inclusion,
`inducedImages_le_standard_at_positiveDepth` handles the induced
generators. `inducedStandardCongruence` at zero puts the first
congruence subgroup of the connected Néron model in the standard
depth-one term, hence in the shallow standard term by antitonicity.
The depth-zero terms are the same connected Néron integral points.
`exists_depthParts` writes any depth as a shallow depth plus a natural
number. Induction on that number uses `minimalCongruentCongruence` and
`inducedStandardCongruence` on the same smooth realizing model.

For an arbitrary torus, `IsTorus.exists_mono_inducedTorus` supplies
an embedding into an induced torus. After passage to a common separable
closure the characters of the induced torus restrict surjectively by
`IsSplitTorus.characterRestrict_surjective_of_mono`. Its positive
standard term thus detects the geometric character subgroup of the
original torus. `minimalCongruentFunctoriality` and the equality for
induced tori put the minimal congruent term in that subgroup.
`minimalCongruentPoints_antitone` puts it in the depth-zero term.
Their intersection is the positive standard term.

For the reverse inclusion let \(L\) be a finite tame extension over
which the torus becomes induced. `minimalCongruentZeroPlus` places
every positive standard point in the positive minimal congruent union.
`InducedPowerTransfer.exists_degree_power_factorization` factors the
degree power through an induced torus. Standard functoriality along the
first map and minimal congruent functoriality along the second then put
the powered point in the required minimal congruent term.
`not_dvd_finrank_of_tame` shows that the degree is prime to the residue
characteristic. `minimalCongruentPoints_mem_of_coprime_pow` recovers
membership of the original point.

The comparison is Corollary B.10.13 of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), printed pp. 691–692,
PDF pp. 722–723. The induced shift uses Proposition B.3.6, and the
degree-power factorization implements the restriction and norm
argument of Proposition B.6.6.
