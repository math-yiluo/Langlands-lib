# Conditional local lifts for analytification fibre products

Author: Worker 790.

`pointHom_changeRing` proves naturality of the Yoneda morphism of a
ring-valued point under change of test algebra. The postcomposition law
`pointHom_map` comes from the published `SpaceAnalytificationEtaleReduction`
module.
`exists_ringPoint_of_isPullback` lifts a compatible pair of ring-valued
points through an algebraic-space pullback. Its proof applies the
pullback universal property to the corresponding morphisms from the
test scheme, and converts the result back to a section.

`exists_lift_of_affine_factorizations` treats a compatible analytic cone
whose legs already factor through two finite polynomial test maps.
It assumes the algebraic square is a pullback, the base algebraic space
is separated, the two lower vertices and base have analytifications, and all
four analytic arrows are compatible with the algebraic arrows on test
points. It constructs the finite polynomial intersection of the two
base-valued test points. The base analytification's affine-test
pullback condition lifts the analytic cone to this affine
intersection. The algebraic pullback gives an intersection-valued point
of the top algebraic space. Composing its analytic test map with the
lift gives the required morphism. Naturality and the given
compatibilities prove the two projection equations.

`IsAnalytification.exists_etale_local_factorization` assumes localized
étale pullback existence with an étale base-changed projection, and
existence of points lifting matching pairs through categorical
pullbacks. Joint surjectivity supplies an affine test chart through the
image of the prescribed source point. Pulling back that chart and
lifting the point gives a source refinement and the desired
factorization. `exists_simultaneous_etale_local_factorization` applies
this twice and composes the two étale refinements, retaining a point
above the original point.

`exists_etale_local_lift` combines simultaneous factorizations with
`exists_lift_of_affine_factorizations`. It therefore gives local lifts
for every compatible cone at every source point, under the two
explicit geometric inputs. It does not prove uniqueness or assert the
final fibre-product statement. No independent affine-analytification
preservation theorem is assumed for this existence step.

## Provenance: internal

These are derived lemmas for the algebraic-space analytification
fibre-product task. They use the published Yoneda and algebraic-space
interfaces together with the explicitly imported, locally proved affine
intersection lemma. The proof follows the stated diagram construction;
no unproved analytic descent or base-change assertion is used.
