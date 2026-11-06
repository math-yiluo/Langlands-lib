# Universal Hom families on the open graph locus

Author: Worker 1656. The imported open isomorphism locus and its étale
descent were developed by Worker 362.

This internal construction takes an actual universal closed relative-torus
subgroup family in the pullback of `H × G` and restricts it to the open
locus where its first projection is invertible. Here `H` is a split torus
and `G` is separated over an arbitrary scheme `S` in universe `u`.
Existence of the universal subgroup family is an explicit hypothesis.

`graphLocus j` is the actual open subscheme of the original parameter
scheme defined by `TorusIsomorphismLocus.opens` for the first projection
of `j`, with the composite structure morphism to `S`. `graphLocusMap j`
is its actual monic inclusion over `S`. The first projection of an
evaluated inclusion is the base change of the original projection
followed by the actual source comparison. Since that comparison is an
isomorphism, invertibility is equivalent to invertibility of the base
change. The open-locus construction guarantees this on `graphLocus j`.
Inverting the first projection therefore gives `graphLocusHom j`, an
actual relative homomorphism. Recovery and composition of subgroup-family
evaluation show that the graph of its evaluation at `a` equals evaluation
of `j` at the composite with `graphLocusMap j`, on every test scheme.

`isUniversal_graphLocusHom` proves the exact Library universal property.
For injectivity, equal evaluated homomorphisms have equal graph subgroups.
The unique-parameter property of the given subgroup family identifies
the two composite parameters in the original parameter scheme; monomorphy
of the open inclusion identifies the original parameters. For surjectivity,
the graph of any actual homomorphism is an admissible closed torus subgroup,
so universality supplies a parameter `c`. Closedness makes the evaluated
inclusion monic. The graph-recovery converse shows its first projection
is invertible. The source is an étale form of a split torus and the
target is the base change of `H`, hence split. The relative-source,
split-target all-test criterion of `IsomorphismLocusEtale` factors `c`
through the open graph locus as an actual morphism over `S`. The graph
evaluation identity and injectivity of the graph construction then
identify the evaluated recovered homomorphism with the supplied one.
No restriction to field-valued points is made in this universal property.

If the original parameter scheme is smooth over `S`, the graph locus is
smooth because its structure map is an open immersion followed by that
smooth morphism. `exists_smooth_universal_of_torusSubgroupFamily` combines
this with the preceding construction.

Finally, `smoothSplitSourceRepresentability_of_torusSubgroupModuli` is a
conditional implication from the exact independent smooth subgroup-moduli
proposition to the exact smooth split-source Hom proposition, in the same
arbitrary universe. A split torus is smooth and affine, so `H × G` is
smooth and affine when `G` is. Applying the assumed subgroup-moduli
proposition to that product supplies the family and smooth parameter
scheme used above. The module does not prove the assumed subgroup-moduli
existence proposition or the unconditional smooth Hom theorem. Its
provenance is internal: it derives this implication from actual graph,
pullback, open-locus and universal-family interfaces already implemented
in the project.
