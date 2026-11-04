# Geometric-connectedness fibre-locus constructibility

Worker 105 states the geometric-component-count-one specialization of
Stacks Lemma 37.28.6, tag 055I. The retained original HTML and its comments
belong to `stacks-fibre-constructibility-local-dimension-2026-11-04`,
SHA-256
`1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`.
The definition of the source's counting function is Lemma 37.28.3,
tag 055F, in the retained `055C.html`: it counts the connected components
after extension of the actual residue field to a separably closed field.
The comments on 055I clarify that these are geometric connected
components. They are not a selection of components of the original
fibre that individually remain connected under field extension.

`GeometricallyConnectedFiberLocalConstructibility` asserts that
`geometricallyConnectedFiberLocus f` is locally constructible for every
finite-presentation morphism of arbitrary schemes in universe `u`.
Finite presentation means local finite presentation, quasi-compactness
and quasi-separatedness of the morphism. All three hypotheses remain
explicit. There is no additional separatedness, affineness, flatness,
properness, smoothness, Noetherianity or surjectivity assumption.

The locus is the existing actual target subset: at `y`, the structure
morphism of the residue-field scheme fibre is geometrically connected.
Mathlib's convention uses `ConnectedSpace` after every field-valued base
change and therefore requires nonemptiness. This is the count-one
specialization of 055I; an empty geometric fibre has count zero and is
excluded. The proposition does not assert constructibility of the
entire component-count function, nor openness of this locus. It is an
unproved proposition definition supplying the exact target for a
separate proof task.

The remaining declarations are proved, derived reductions. Local
constructibility becomes global constructibility when the target is
quasi-compact and quasi-separated, by the pinned Mathlib theorem
`IsLocallyConstructible.isConstructible`. Schemes supply its prespectral
space hypothesis. For any morphism, the existing combined nonempty,
geometrically connected, pure-dimensional fibre locus equals the
intersection of the geometric-connectedness and componentwise
pure-dimension loci. Thus local or global constructibility of the two
actual factors implies the corresponding property for the combined
locus. These two intersection lemmas need no finiteness assumption
because their factor conclusions are explicit premises. Pure dimension
retains the existing componentwise meaning, with empty fibres satisfying
that factor vacuously; the geometric-connectedness factor excludes them.

This prerequisite serves the final clause of Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed
pp. 5–6, Theorem 3.4(2), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Neither the general local-constructibility target, pure-dimension
constructibility, nor Conrad's unrestricted filtered-descent theorem
is proved here.
