# Extensions of tori with Levi centralizers

Let `j : P ⟶ G` be a closed subgroup map over an arbitrary field, and let
`l : L ⟶ P` and `m : M ⟶ P` be rational Levis of the same group `P`.
Suppose the actual composites `l ≫ j` and `m ≫ j` represent the whole-group
centralizers of commutative group maps `a : A.toGrp ⟶ G` and
`b : B.toGrp ⟶ G`, respectively. An actual map `f : A.toGrp ⟶ B.toGrp`
with `f ≫ b = a` then forces the two all-test centralizers to agree.

`IsRationalLeviSubgroup.centralizerExtensionFactor` constructs the actual
map `B.toGrp ⟶ L` whose composite with `l ≫ j` is `b`. It is central in `L`;
if `b` is closed, it is closed in `L`. If `b` is a split subtorus, this factor
is a central split torus of `L`. No torus or splitness assumption on the source
is needed for centralizer equality or centrality of the factor.

For a specified ground-field solvable radical `r : R ⟶ P`, with
`IsSolvableRadical r`, and a closed torus `b`,
`centralizerExtensionRadicalFactor` constructs an actual closed map
`B.toGrp ⟶ R`. Its composite with `r ≫ j` is exactly `b`.

## Implemented proof

Centralizer contravariance along `f` gives
`range (m ≫ j) ≤ range (l ≫ j)`. The preliminary arbitrary-base lemma
`SubgroupFunctor.range_comp_le_iff_of_mono` cancels the monomorphism `j`
from this inclusion on each test scheme. The imported
`IsRationalLeviSubgroup.range_eq_of_le` from `Rational.LeviInclusionRigidity`
then proves `range m = range l`. Postcomposition with `j` gives equality of
the two represented centralizers.

The original inclusion `l ≫ j` therefore represents the centralizer of `b`.
The existing `torusCentralizerFactor` supplies the actual factor into `L`,
its ambient identity, and centrality in `L`. Its closedness follows from
closedness of `b` and `l ≫ j`. The radical factor is the existing
`centralTorusRadicalFactor` applied to this now central closed Levi torus.
The two composite identities give its stated ambient identity.

## Provenance and remaining geometry

This is an internal construction from represented all-test centralizers,
Levi inclusion rigidity, and central Levi torus containment in the solvable
radical. It assumes the two specified rational Levis and their actual
centralizer representations. It introduces no claim of their existence.

For the minimal-parabolic application, constructing a compatible refined
parabolic and identifying it with `P` by minimality must precede this result.
Neither that geometric construction nor ambient maximal splitness is proved
here. In particular, no structural premise has been added to the unchanged
`MinimalParabolicLeviCentralizerStatement`.
