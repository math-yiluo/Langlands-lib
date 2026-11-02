# Rational points of a represented standard Levi

Author: Worker 450.

This module gives the explicit rational-point identification needed to apply the
actual center compactness statements to the same standard Levi used by the
parabolic and building interfaces. It does not choose another reductive group.

For the existing subgroup functor `standardLevi i ν J`, a morphism `j : M ⟶ G`
must satisfy `(standardLevi i ν J).IsRepresentedBy j`. This means that the
underlying morphism is mono and that its image equals `standardLevi i ν J` on
**every** test scheme. Closedness and connected reductivity are separate
hypotheses in the topology statement. The module does not assert existence of
such a representation or prove that a represented standard Levi is reductive;
those remain algebraic prerequisites.

`standardLeviRationalPointsMap` sends `x : M(F)` to `x ≫ j.hom.hom`,
regarded as an element of `standardLeviPoints i ν J`. Its membership proof uses
the all-test image equality at the identity test `Spec F`. The helper
`standardLeviRationalPointsMap_bijective` proves injectivity by cancellation of
the mono and surjectivity by that image equality.
`standardLeviRationalPointsEquiv` bundles this very map as a group isomorphism;
the two `_val` lemmas display its actual underlying rational-point map. The
inverse is the unique preimage along `j`, selected by `MulEquiv.ofBijective`.
These are internal constructions from the published definitions, rather than
new structural results quoted from the literature.

`standardLeviPointTopology` is the topology induced from
`rationalPointTopology F G.X` by the subtype inclusion
`standardLeviPoints i ν J → G(F)`. It is not defined by transporting the
topology of `M(F)` across the equivalence. The separately named Prop
`StandardLeviPointTopologyComparison` says the explicit equivalence is a
homeomorphism when `M(F)` has its canonical rational-point topology and the
standard Levi subgroup has this inherited topology. No topology instance or
homeomorphism assertion is added implicitly.

`StandardLeviPointTopologyComparisonStatement` closes that target over every
topological field and actual connected reductive `G`, a maximal split torus
`i`, a generic cocharacter `ν`, and a subset `J` of the resulting simple
relative roots. It requires an actual closed representation `j` and an actual
connected reductive `M`. It has no compactness premise and no assumption that
the comparison already holds. The general topological-field scope is valid
because a closed immersion of affine schemes induces an embedding for the
evaluation topology; no local compactness or separation of the field topology
is needed for this comparison target. The statement is **not proved here**.

The structural source is Borel–Tits, *Groupes réductifs* (1965), §4.2(i)–(ii),
printed pp. 85–87 (PDF pp. 32–34), and §5.12, printed p. 99 (PDF p. 46):
standard relative parabolics have the corresponding Levi centralizers, with
the relative-field scope explained in §5.12. Renard, *Représentations des
groupes réductifs p-adiques*, 9 July 2026 edition, V.3.1, printed p. 110
(PDF p. 116), identifies Levi subgroups as centralizers of their split
components; V.3.8, printed p. 111 (PDF p. 117), keeps the same fixed maximal
split torus in each standard Levi. These passages motivate which actual
subgroup is being represented. They do not supply the implemented
all-test-to-rational-point calculation or the unproved topology comparison.

For the point topology, Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Remark 2.2.2, printed p. 70 (PDF p. 101), uses the topology induced
from affine coordinates and refers to Conrad for its intrinsic form. The
formal topology used here is the Library's existing affine evaluation
topology, transported to the identity-test convention by
`rationalPointTopology`. The 1 November 2024 corrections, PDF pp. 24–25,
replace the initial §2.2 hypotheses by the Henselian convention, repair
Lemma 2.2.5 and the signs of the valuation homomorphisms, and distinguish the
torus Iwahori and maximal bounded subgroups. This module invokes none of
those corrected valuation or boundedness assertions.

No characteristic-zero, perfect-field, smooth-center, split or quasi-split
hypothesis is imposed. This identification can therefore be used in both
mixed and equal characteristic when the compactness statements are
specialized to nonarchimedean local fields.
