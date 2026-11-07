# Actual geometric-lemma data from original common-torus factors

`geometricLemmaIntersectionDatumOfTorusFactors` constructs the actual
intersection datum for prescribed parabolic triples and a prescribed rational
point `z`. Its geometric inputs are a prescribed ambient maximal split torus
and factors through the source Levi `M` and the target Levi conjugated by `z`.
The universal `ParabolicDynamicStatement` remains an explicit hypothesis.

The proof first transports the original torus into the target frame by
`Int(z⁻¹)`. The supplied target factor is exactly this transported map, and
the supplied source factor has the same ambient composite in the conjugated
source triple. Applying the published
`exists_cocharacter_parabolic_triple_in_torus` twice chooses cocharacters in
this same original torus. That theorem derives the actual radical equality
from the proved dynamic geometric radical theorem. The resulting six
all-test dynamic equalities instantiate
`geometricLemmaIntersectionDatumOfCommonCocharacters`, which constructs both
actual intersection triples, conjugation and its rational-point
homeomorphism.

The theorem
`representedGeometricLemmaGeometry_of_doubleCoset_of_parabolicDynamic`
then derives the existing `RepresentedGeometricLemmaGeometryStatement` from
the explicit `RepresentedParabolicDoubleCosetStatement` and
`ParabolicDynamicStatement`. The first hypothesis supplies finite actual
rational double cosets and a torus-adapted representative for each. The
constructor supplies each actual datum, and the existing finite enumeration
lemma assembles them. An additional universal Levi-intersection-structure
hypothesis is thereby discharged.

This is an internal assembly of published structural results and the actual
common-cocharacter intersection construction. It proves neither of the two
universal premises, a representation-theoretic geometric filtration, nor
native coefficient Jacquet finiteness. Those remain explicit obligations of
their respective consumers.
