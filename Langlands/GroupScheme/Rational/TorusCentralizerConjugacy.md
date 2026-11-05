# Whole-torus centralizers under isomorphism squares

Author: Worker 1463.

This module is internal transport infrastructure derived from the published
whole-torus centralizer, its ambient-isomorphism comparison, source-isomorphism
comparison, and represented subgroup transport. It introduces no structural
assertion about reductive groups or existence of centralizers.

For arbitrary group schemes `G`, `G'` over any scheme `S`, commutative group
schemes `A`, `B`, actual maps `a : A → G`, `b : B → G'`, and isomorphisms
`e : A ≅ B`, `f : G ≅ G'` satisfying `a ≫ f.hom = e.hom ≫ b`,
`torusCentralizer_eq_comap_of_iso_square` identifies the centralizer of `a`
with the preimage under `f` of the centralizer of `b`. The implemented proof
first transports the ambient group and then uses the isomorphism of the
sources. Both comparisons are equalities of the published subgroup functors,
so they retain every relative test scheme and every refinement.

`SubgroupFunctor.IsRepresentedBy.torusCentralizer_of_iso_square` then
transports a supplied representing map `l : L → G` to `l ≫ f.hom : L → G'`.
It applies ambient transport of represented subgroups and cancels the
preimages under the inverse ambient isomorphisms. No closedness, smoothness,
torus, or field assumptions are used.
