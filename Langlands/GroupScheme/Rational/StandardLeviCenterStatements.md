# Actual center targets for the same represented standard Levi

Author: Worker 450, with source-route guidance from Worker 101. The imported
`CenterSplitComponent` definitions were constructed by Worker 101.

This module specializes WST-CEN-01 to the existing all-test subgroup functor
`standardLevi i ν J` and its rational-point subgroup `standardLeviPoints i ν J`.
It adds two separately named, unproved Prop targets:
`StandardLeviCenterCompactnessStatement` and
`StandardLeviRationalCenterComparisonStatement`. `StandardLeviCenterStatements`
is their conjunction. These are statements to be proved in successor work.

Both closed targets quantify over every nonarchimedean local field `F`, an
actual connected reductive ambient group `G`, a maximal split torus `i`, a
generic cocharacter `ν`, and a subset `J` of the resulting simple relative
roots. They then require an actual connected reductive `M`, a closed inclusion
`j : M ⟶ G`, and `(standardLevi i ν J).IsRepresentedBy j`. This last witness
identifies the image with the same standard Levi on every test scheme; it is
stronger than agreement only on rational points. No different reductive group
is substituted. The existence of this representation and reductivity of a
constructed representative remain with the algebraic owners. The targets
impose no characteristic-zero, perfect-field, split, quasi-split, or
smooth-center hypothesis, so their local-field scope includes mixed and equal
characteristic.

The compactness target quantifies over every actual morphism `a : A.toGrp ⟶ M`
with `hA : IsSplitComponent a`. Its conclusion is compactness of
`CentralPointQuotient a hA.isCentralSplitTorus.isCentral`. This is the quotient
of the full scheme-center rational points by the image of the actual map
`A(F) → Z(M)(F)`. The center retains its all-test centrality condition, including
nonreduced test schemes; it is not replaced by its reduced identity component
or a torus. The topology on `M(F)` is the canonical evaluation topology,
the center has its inherited subgroup topology, and the quotient has the
explicit `centralPointQuotientTopology`. Compactness is the conclusion and is
never assumed.

The map `standardLeviSchemeCenterToCenter` first includes `Z(M)(F)` in the
abstract center of `M(F)`, then applies `Subgroup.centerCongr` to
`standardLeviRationalPointsEquiv i ν J j hj`. Its value, after both subtype
inclusions into `G(F)`, is exactly `rationalPoints.map j z.val`; the `_val`
lemma proves this by reduction. For any actual central `a : H ⟶ M`,
`standardLeviCentralRationalPointsMap` composes this map with
`centralRationalPointsMap a ha`. Its underlying ambient value on `x` is
`rationalPoints.map j (rationalPoints.map a x)`, as its `_val` lemma states.
Taking `H = A.toGrp` gives the consumer's actual split-component map.
These are internal constructions from the two imported point-map modules.

`standardLeviAbstractCenterTopology` is the subgroup topology of the abstract
center of `standardLeviPoints i ν J`, where the latter inherits its topology
from the canonical topology of `G(F)`. It is defined independently of the
topology on `M(F)`. `StandardLeviRationalCenterComparison` says that the
explicit center map is a homeomorphism from `schemeCenterPointTopology M`
to this topology. Its closed statement assumes neither equality of centers
nor a homeomorphism. A proof needs the rational-center comparison for actual
connected reductive groups over these infinite fields (typically through
rational-point density) and the canonical-versus-inherited point topology
comparison. Neither proof is supplied here.

Milne, *Algebraic Groups* (2017), Proposition 1.93, printed p. 34 /
PDF p. 50, characterizes centralizer points using a dense set of points of
a smooth algebraic subgroup. Theorem 17.93(b), printed p. 382 / PDF p. 398,
gives rational-point density for connected reductive groups over infinite
fields without a perfect-field premise. Together these give the source route
from commutation on `M(F)` to membership in its full scheme center.
Remark 1.97, printed p. 35 / PDF p. 51, explicitly allows a nonsmooth center
even when the ambient group is smooth. The formal density-to-all-test-center
bridge and its topology comparison remain proof obligations here. The
author's errata snapshot of 2 November 2026 contains no correction to these
three passages.

For the structural identification of the same standard Levi, the original
sources are Borel–Tits, *Groupes réductifs* (1965), §4.2(i)–(ii), printed
pp. 85–87 / PDF pp. 32–34, and §5.12, printed p. 99 / PDF p. 46; and Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.3.1, printed p. 110 / PDF p. 116, and V.3.8, printed p. 111 / PDF p. 117.
Renard identifies a Levi as the centralizer of its split component and keeps
the fixed maximal split torus inside each standard Levi. These motivate the
representation hypothesis, rather than proving its existence in Lean.

For compactness, Renard V.2.5, printed p. 107 / PDF p. 113,
discusses the split and anisotropic parts of a torus. V.2.6, printed
pp. 107–108 / PDF pp. 113–114, states finiteness of `G/(⁰G A_G)` and
compactness of `⁰G ∩ Z(G)`; its proof uses the finite component data of the
center and cocompactness of the product of its anisotropic part with `A_G`.
This is the source route for the full central point quotient, rather than
a proof that a finite isogeny has finite cokernel on local-field points.
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Theorem 2.2.9,
printed pp. 71–72 / PDF pp. 102–103, proves boundedness of the rational points
of an anisotropic connected reductive group. Fact 2.2.3, printed p. 70 /
PDF p. 101, compares boundedness and compact closure over a locally compact
field. Remark 2.2.2 on that page gives the affine-coordinate point topology.
Lemma 2.5.7 and Proposition 2.5.8, printed p. 88 / PDF p. 119, describe the
valuation lattice and maximal bounded subgroup of a torus.

A possible proof route constructs the central quotient by the split
component, applies anisotropic compactness with the necessary finite
component and infinitesimal data retained, and proves the actual
rational-point and topology comparison with the quotient used here. Split
kernel descent via Hilbert 90 is one possible ingredient for rational-point
surjectivity, but no such bridge is asserted in this module. The quotient of
rational points is not identified with the rational points of a scheme
quotient without that proof. In particular a finite or isogeny morphism alone
does not imply a finite rational-point cokernel in equal characteristic.
Kaletha–Prasad §2.5.21, printed p. 92 / PDF p. 123, also records failure of
surjectivity on bounded subgroups; §2.6.3, printed p. 94 / PDF p. 125, warns
that relevant root kernels need not be smooth. These reinforce the need to
retain the full center and the actual point map.

The authors' *Corrections and additions*, 1 November 2024 version,
PDF pp. 24–25, amend the initial §2.2 hypotheses, Lemma 2.2.5, valuation
signs and the torus Iwahori/maximal-bounded distinction. No corrected
valuation formula or identification of those two subgroups is used here.
The literature passages explain the intended route; this contribution
constructs the explicit maps and states the remaining targets.
