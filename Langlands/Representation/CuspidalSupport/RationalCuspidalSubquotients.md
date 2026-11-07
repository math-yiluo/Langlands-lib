# Actual cuspidality passes to arbitrary smooth subquotients

Worker 1751. This internal result connects ordinary cuspidality with the
all-cuspidal-subquotient factor used by the actual category decomposition.

`CuspidalSubquotientClosure` states that vanishing of every actual normalized
Jacquet module in the supplied family passes to every actual smooth
subquotient. The source and subquotient share their carrier universe, which
is independent of the group and test-index universes.

`cuspidalSubquotientClosure_of_compactExhaustion` proves this assertion when
every tested radical is exhausted by compact subgroups. Express an actual
subquotient by an actual injection into the source followed by an actual
surjection onto the subquotient. The published compact-exhaustion theorem
makes the localized injection injective. Localization preserves surjectivity
without an exhaustion premise. Normalization keeps these underlying maps.
The first Jacquet carrier embeds into the zero Jacquet carrier of the source,
so it is a subsingleton; its surjective image is also a subsingleton. This
proves vanishing for each test.

`rationalAllCuspidalSubquotientProperty_iff_isCuspidal` specializes to the proper
actual standard parabolics of the rational-point group. The published
standard-cocharacter comparison and dynamic-unipotent compact containment
discharge exhaustion for every tested radical. Thus an ordinarily cuspidal
object has the existing all-cuspidal-subquotient property. The converse applies
that property to the object's identity subquotient.

The structural standard-family hypotheses remain explicit. No admissibility,
finite dimension, finite generation or finite length is assumed, and no
whole-category decomposition, generator property or compression stability is
proved here.
