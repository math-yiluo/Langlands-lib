# Common split tori and conjugacy inside minimal parabolics

Author: Worker 1262.

This module states two geometric prerequisites for rational Bruhat covering.
They concern actual connected reductive group schemes over any field
`k : Type u`. They are unproved proposition definitions at the full
universe scope.

The original source is Borel and Tits, *Groupes réductifs* (1965), source ID
`borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.

`ParabolicIntersectionCentralizerStatement` is 4.18, printed p.92
(PDF p.39). For any two actual rational parabolics `j : P ⟶ G` and
`j' : P' ⟶ G`, it asks for an actual torus homomorphism `i : T.toGrp ⟶ G`
which is a maximal split torus of `G` and whose whole-torus centralizer
is contained in both parabolics. The centralizer and the two containments
use the existing subgroup functors on every test scheme. The source's
intersection formulation is expressed as these two simultaneous inclusions.
No hypothesis that the two parabolics are minimal is required.

`MinimalParabolicSplitTorusConjugacyStatement` is a derived consequence of
rational Levi conjugacy in 3.14, printed p.80 (PDF p.27), together with
4.15(b) and 4.16, printed pp.91–92 (PDF pp.38–39). It concerns a fixed
actual minimal parabolic `j : P ⟶ G`, two maximal split tori of the
ambient group `i : T.toGrp ⟶ G` and `i' : T'.toGrp ⟶ G`, and specified
factorizations `f ≫ j = i` and `f' ≫ j = i'`. It asks for `p : P(k)` and
an actual torus isomorphism `e : T.toGrp ≅ T'.toGrp` satisfying
`f ≫ (P.innerIso p).hom = e.hom ≫ f'`.

The derived source route uses 4.16 to place both split tori in the radical
of `P`, the description of their centralizers as rational Levi subgroups,
and 3.14 to conjugate those Levi subgroups by a rational point in the
unipotent radical. The largest split torus in the center of a Levi subgroup
then identifies the transported split tori. These geometric facts remain
proof obligations. Ambient conjugacy of maximal split tori in 4.21 is
insufficient for this conclusion, because the conjugating point must lie
in `P(k)`.

The factorization equations and conjugacy conclusion are equations of
actual group scheme homomorphisms. The statement therefore records the
scheme normalizer information needed for Bruhat covering even over finite
fields. It imposes no splitness, perfectness, characteristic, rational
surjectivity, or cardinality assumption on the ground field.
