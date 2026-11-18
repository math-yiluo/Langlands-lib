# Lifting a multiplicative-type group from an étale local model

The map on bases is a surjective closed immersion and the square of covers
is cartesian. The induced maps on the sources and on both Čech overlaps are
also surjective closed immersions. The two endpoints of every required Hom
set are base changes of the multiplicative-type group on the original
cover. Full faithfulness for those groups supplies the Hom bijections which
lift the descent datum.

For an affine base and an étale surjective cover, take an affine
multiplicative-type group on the cover and an isomorphism of its reduction
with the local pullback of the special-fibre group. This isomorphism transfers
the special-fibre group's canonical datum to the reduced local model. Apply
the datum lift and effective affine descent to construct a group over the
original base. Its multiplicative type descends through the cover, hence it
is flat. After reduction the descended group and the special-fibre group
solve the same datum, so the identity on the local model descends to an actual
isomorphism between them.

The proof implements the descent part of SGA 3, Exposé X, Proposition 2.1
(registered source `sga3-expose-x-gille-polo-2009`, pp. 66–67). The local model
is supplied as a hypothesis here.
