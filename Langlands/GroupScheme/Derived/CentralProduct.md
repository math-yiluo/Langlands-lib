# Full derived subgroups of fpqc central products

Over an arbitrary scheme `S`, let `i : Z ⟶ G` be a central group-scheme
homomorphism and `d : D ⟶ G` a closed subgroup inclusion. Assume the actual
multiplication morphism `Z × D ⟶ G` is quasi-compact, flat and surjective.
If `derivedSubgroup D = ⊤`, then `d` represents the full derived subgroup of
`G`. All ranges, centrality and equalities use every test scheme over `S`.
No smoothness, connectedness, affineness or field hypothesis is imposed.
The map `i` need not be a closed inclusion, and its source need not be
commutative; centrality concerns its full image in `G`.

`commutator_subgroupMultiplication_of_isCentral` computes commutators of
product points. Central factors cancel, leaving the image under `d` of
the commutator of the two `D` coordinates. To prove
`containsCommutators_range_of_fpqc_centralProduct`, apply this identity
to the universal pair of product points. The square of the multiplication
homomorphism is an effective epimorphism of schemes by the published fpqc
lemma. The commutator map of `G` therefore factors through the closed
immersion `d`, by the published diagonal-lift lemma. Evaluating that
factorization on any pair of test points proves that every commutator
lies in the full range of `d`.

`isDerivedSubgroup_of_fpqc_centralProduct` gives the stated identification.
Minimality of the full derived subgroup gives containment in `range d`.
For the reverse containment, apply full derived-subgroup functoriality to
`d` and use the assumed perfectness of `D`.

`centralProductDerivedIso` constructs the actual isomorphism from `D` to
any supplied closed representative `e : E ⟶ G` of the full derived subgroup.
`centralProductDerivedIso_hom_comp` states that its forward map followed
by `e` is precisely `d`.

This is internal support derived from the Library's unchanged
intersection definition, full functoriality, fpqc effective epimorphism
and representative comparison lemmas. It constructs no factorization
of a particular reductive group and proves no semisimple perfectness
or normal-complement theorem. Those remain separate obligations.

Authorship: Worker 1616.
