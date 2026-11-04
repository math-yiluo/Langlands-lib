# The actual centralizer-sharp product in a parahoric

This derived adapter constructs `parahoricProductMap` from the supplied
`P.centralizerZero × P.sharpFixer Ω` onto the actual full `P.parahoric Ω`.
It proves surjectivity, equality of the parahoric carrier with the set product
of these factors in either order, and normality of the sharp fixer inside the
full parahoric. It makes no injectivity assertion.

The scope is every actual `ParahoricBuildingData` over a nonarchimedean local
field at arbitrary universe `u`, in either characteristic. The result holds for
every apartment subset, including the empty subset. It uses V 6 already bundled
in the datum and the actual centralizer-zero norm-kernel comparison. It needs
no extra apartment axiom, topology compatibility, compactness or openness premise.

## Sources and provenance

KP Definition 7.4.1(4), *Bruhat–Tits Theory: A New Approach* (2023), printed
p.255 / PDF p.286, describes the full parahoric as the product of centralizer
zero and the sharp fixer. The Library's `KPParahoric` construction forms the
join of those two subgroups. This module proves that the join equals the set
product without changing either subgroup. The original page was read directly.
The authors' 1 November 2024 corrections, PDF pp.33–35, were also read; the
correction before Remark 7.4.2 simplifies singleton notation and does not change
the two factors of Definition 7.4.1(4).

This is a derived algebraic consequence of the existing actual-object
`KPBuilding`, `KPCentralizerCompatibility`, `KPZeroNormKernel` and `KPParahoric`
APIs and Mathlib's subgroup-normalizer product lemmas. It does not assume the
source product equality or introduce a replacement zero subgroup.

## Implemented proof

For `B : ValuationBuildingData`, V 6 makes every element of the actual
centralizer's rational norm kernel act trivially on the apartment. It therefore
preserves every apartment subset `Ω`. The existing normalizer covariance of the
sharp fixer then shows that its image in `G(F)` normalizes `B.sharpFixer Ω`.
The actual centralizer-zero norm-kernel inclusion specializes this to
`P.centralizerZero`.

A subgroup normalizing another subgroup has its join equal to their set
product. Applying that result gives `coe_parahoric_eq_mul`; the same normalization
permits the reverse order. Unpacking the mapped centralizer factor gives
`mem_parahoric_iff`, and this proves surjectivity of the explicitly defined
multiplication map. The sharp fixer is normal in the join by the same
normalizer inclusion.

The result is a two-factor product comparison. It supplies no finite ordered
root-factor decomposition of the sharp fixer and no compactness, boundedness,
closedness or openness result for either factor or for the full parahoric.
Those remain separate obligations for the chamber compact-openness target.
