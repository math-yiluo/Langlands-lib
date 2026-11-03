# Center targets for the canonical standard Levi representative

Author: Worker 450, with statement-scope and source-route guidance from Worker 101.

This module specializes the published `StandardLeviCenterStatements` to the
specific group scheme `Standard.leviScheme i ν J` and inclusion
`Standard.leviHom i ν J`. The published theorem
`Standard.isRepresentedBy_leviHom` identifies this representative with the same
`standardLevi i ν J` on every test scheme. Its closedness is supplied by
`Standard.isClosedSubgroup_leviHom`. Thus the new targets do not quantify over
an unspecified substitute for the common standard Levi.

`CanonicalStandardLeviCenterCompactnessStatement` and
`CanonicalStandardLeviRationalCenterComparisonStatement` are separate unproved
Prop definitions; `CanonicalStandardLeviCenterStatements` is their conjunction.
Both quantify over every nonarchimedean local field `F`, actual connected
reductive `G`, maximal split torus `i : T → G`, generic cocharacter `ν`, and
subset `J` of the resulting simple relative roots. There is no characteristic
restriction or perfect-field premise. Actual connected reductivity
`hM : IsConnectedReductive (Standard.leviScheme i ν J)` remains an explicit
input, as does each actual split component in the compactness target.
Compactness, equality of centers and topology comparison remain conclusions.

The compactness target applies to every actual
`a : A.toGrp ⟶ Standard.leviScheme i ν J` with `hA : IsSplitComponent a`.
It states compactness of `CentralPointQuotient a
hA.isCentralSplitTorus.isCentral`, using the existing
`centralPointQuotientTopology`. The numerator is the full all-test scheme-center
functor evaluated on `F`; the denominator is the image of the actual map
`A(F) → Z(M_J)(F)`. The center topology is inherited from the canonical
evaluation topology of `M_J(F)`, and the quotient has the quotient topology.
Neither a reduced center nor its identity torus replaces this numerator.
Nonreduced centers and finite component data remain within the scope.

`canonicalStandardLeviSchemeCenterToCenter` is the published
`standardLeviSchemeCenterToCenter` with this exact representative, inclusion
and representation witness substituted. It maps the full scheme-center
points into the abstract center of `standardLeviPoints i ν J`. Its ambient
value is exactly `rationalPoints.map (Standard.leviHom i ν J) z.val`.
`canonicalStandardLeviCentralRationalPointsMap` composes it with the actual
central point map of `a : H → M_J`; its ambient value is
`leviHom(F)(a(F)(x))`. The two `_val` lemmas are definitional reductions.
If supplied with `g : H → T` and the actual equality
`g ≫ i = a ≫ Standard.leviHom i ν J`, the
`_val_of_factorization` lemma gives the same point as `i(F)(g(F)(x))`.
Its proof applies the equality to the underlying morphisms and uses
associativity of composition. It constructs no such factorization.

`CanonicalStandardLeviRationalCenterComparison` is precisely the published
`StandardLeviRationalCenterComparison` for this representative and inclusion.
It asserts that the explicit center map is a homeomorphism from
`schemeCenterPointTopology M_J` onto the abstract center of
`standardLeviPoints i ν J`, with its subgroup topology inherited from canonical
`G(F)`. These topologies are defined independently. Surjectivity onto the
entire abstract center, and continuity in both directions, are part of the
target. The comparison is not made automatic by transporting a topology
along the proposed map.

The separate published `StandardLeviSplitComponentStatement` names the
remaining structural existence result: this same `M_J` is connected
reductive, and there exist `A`, `a : A → M_J` and `g : A → T` with
`IsSplitComponent a` and `g ≫ i = a ≫ Standard.leviHom i ν J`.
Its file contains a conditional reduction to other structural targets, not
a proof of their premises or of this existence assertion. Closed
representability alone does not supply these inputs. This module neither
chooses an `A_J` nor proves that an arbitrary supplied split component has
such a factorization. Once actual structural witnesses are available, the
compactness target covers the supplied `a` and the factorization lemma
records its precise map into the common ambient torus.

The derivation is internal: substitute the published representative and its
all-test witness into the published same-Levi center maps and statements.
No structural existence or center-target proof is supplied here. The
original-source routes are those of `StandardLeviCenterStatements`, with
the following exact passages retained for this specialization.

Borel–Tits, *Groupes réductifs* (1965), §4.2(i)–(ii), printed
pp. 85–87 / PDF pp. 32–34, and §5.12, printed p. 99 / PDF p. 46, give the
standard-Levi structural setting. Renard, *Représentations des groupes
réductifs p-adiques*, 9 July 2026 edition, V.3.1, printed p. 110 /
PDF p. 116, identifies Levi factors as centralizers of their split components;
V.3.8, printed p. 111 / PDF p. 117, keeps the fixed maximal split torus in
each standard Levi. These identify the intended structural role, without
discharging the actual reductivity and split-component existence target.

For compactness, Renard V.2.5, printed p. 107 / PDF p. 113, describes
split and anisotropic torus factors. V.2.6, printed pp. 107–108 /
PDF pp. 113–114, uses finite center-component data and cocompactness of the
anisotropic part together with the split component to obtain compactness
of `⁰G ∩ Z(G)` and finiteness of `G/(⁰G A_G)`.
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §2.2.1–2.2.3,
printed p. 70 / PDF p. 101, gives the affine-coordinate topology and
boundedness/compactness comparison. Theorem 2.2.9, printed pp. 71–72 /
PDF pp. 102–103, gives anisotropic reductive boundedness. Lemma 2.5.7 and
Proposition 2.5.8, printed p. 88 / PDF p. 119, describe torus valuation
lattices and maximal bounded subgroups. A proof of the target still needs
the full central quotient construction, its component and infinitesimal
data, and the actual rational-point and topology bridge. This module does
not identify a quotient of rational points with points of a scheme
quotient or infer finite rational-point cokernel from an isogeny.
Kaletha–Prasad §2.5.21, printed p. 92 / PDF p. 123, records a failure of
surjectivity on bounded subgroups; §2.6.3, printed p. 94 / PDF p. 125,
exhibits nonsmooth root kernels.

For the center comparison, Milne, *Algebraic Groups* (2017),
Proposition 1.93, printed p. 34 / PDF p. 50, compares centralizer points
using a dense point set of a smooth algebraic subgroup. Theorem 17.93(b),
printed p. 382 / PDF p. 398, gives density of rational points of a connected
reductive group over an infinite field without requiring perfectness.
Remark 1.97, printed p. 35 / PDF p. 51, retains nonsmooth centers even for
smooth ambient groups. The density-to-all-test-center and topology
comparisons remain proof obligations.

The Kaletha–Prasad corrections dated 1 November 2024, PDF pp. 24–25,
amend the §2.2 hypotheses, Lemma 2.2.5, valuation signs and the
Iwahori/maximal-bounded distinction. This specialization uses no disputed
valuation formula or identification of those subgroups. Milne's complete
official errata snapshot retrieved 2 November 2026 contains no correction
to the three cited Milne passages.
