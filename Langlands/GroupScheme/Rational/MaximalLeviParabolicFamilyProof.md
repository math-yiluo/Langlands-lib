# Selecting the finite family from the actual parabolic count

`maximalLeviParabolicFamily` proves exactly
`Langlands.GroupScheme.MaximalLeviParabolicFamilyStatement`. It uses the actual
parabolic count and rational conjugacy transport, without a classification of
standard parabolics or an association theorem for representations.

The proof forms the subtype of subgroup functors which are images of actual
rational parabolics with the fixed embedded Levi `l ≫ p`. It chooses an actual
presentation for each image. An injection from `Fin 3` into this subtype would
contradict `maximalLeviParabolicCount` applied to those presentations.

A finite selection lemma first selects the original image. If every image is
rationally conjugate to it, that singleton is the desired family. Otherwise the
lemma selects a nonconjugate second image. Any image conjugate to neither would
be distinct from both, yielding the forbidden injection from `Fin 3`. The
selected images are pairwise nonconjugate, so their actual presentations have
the required separation. The rational Levi predicate supplies matching
geometric radicals and multiplication isomorphisms.

For the general coverage assertion, the specified Levi isomorphism and
conjugation equation let the proof postcompose the new parabolic inclusion
with the inverse inner automorphism. The resulting parabolic has the fixed
embedded Levi and belongs to the subtype. Its selected conjugacy representative
also covers the original parabolic, by transitivity of rational conjugacy.

This is the internal derived structural step described in the paired statement.
It supplies no geometric filtration or representation-theoretic detection.

The companion
[represented length reduction](../../Representation/Exponents/MaximalLeviSupercuspidalGeometricReduction.md)
uses this family with the separately proved actual-image survivor budget and
Worker 4949's detection transport. Its final theorem reduces the original
represented maximal-Levi length bound to the exact represented geometric lemma
and the objectwise cuspidal/remainder splitting. A further theorem supplies the
published geometric lemma, leaving splitting as its only premise. The helper pairs retain the original
transport design of Worker 1281 and the VI.5.3(ii) reduction of Worker 1781.
