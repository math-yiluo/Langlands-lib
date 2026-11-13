# Character restriction on the coroot annihilator

This internal supporting development proves the first conjunct of the actual
standard-parabolic form of Renard V.3.18. The source is David Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026, V.3.13–V.3.18
(PDF pp.117–121).

For a positive definite symmetric real bilinear form, each subspace complements
its orthogonal complement. `positiveFormProjection` is the associated linear
projection. A separate linear algebra lemma proves that a complement of the
kernel of a surjective map has exactly one preimage of each vector.

For actual split tori, perfect real character/cocharacter duality turns an
injective cocharacter map into a surjective character restriction map.
If the cocharacter image is the annihilator of a selected root set, double
annihilation identifies the restriction kernel with the real span of those
roots.

The final theorem applies the published standard-Levi central-directions
theorem to the specified compatible Levi and its split component. The factor
map it supplies equals the specified map, by monicity of the maximal split
torus inclusion. The coroot annihilator is the orthogonal complement of the
restriction kernel by the invariant-form coroot identity. The general linear
algebra lemma therefore gives exactly the restriction bijection asserted in
the first conjunct, with no added hypotheses.
