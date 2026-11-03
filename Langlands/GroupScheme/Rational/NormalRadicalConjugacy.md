# Conjugation transport through a represented normal subgroup

Author: Worker 1264.

This is an internal construction derived from the published all-test
subgroup-functor and conjugacy interfaces. It assumes normality and an
actual representation of the subgroup; it asserts no structural existence
or conjugacy theorem.

For a homomorphism `r : R → P` representing a normal subgroup functor `F`,
`SubgroupFunctor.IsRepresentedBy.conjugateFactor` takes `b : H → R` and a
base point `g : P(S)` to a homomorphism `H → R`. Normality puts the range of
`b ≫ r ≫ Int(g)` inside `F` on every test scheme. The published
`factorHom` construction gives the unique factorization through `r`.
`conjugateFactor_comp` and `conjugateFactor_unique` record its composite
and uniqueness. `conjugateFactor_comp_ambient` uses naturality of inner
automorphisms to retain the exact conjugation equation after any further
ambient homomorphism `j : P → G`.

`torusCentralizer_eq_comap_of_iso` specializes the published transport of
centralizers of subgroup ranges, using the equality between the
whole-torus centralizer and the centralizer of its range. It holds over
any base and on every test scheme and refinement.

Over an arbitrary field,
`SubgroupConjugate.exists_maximalSplitTorus_centralizer` transfers a supplied
centralizer presentation for `l : L → P` to a supplied rationally conjugate
map `l' : L' → P`. Its input torus factors through the specified `R`, is
maximal split in `G`, and has whole-torus centralizer `range (l ≫ j)`.
The output has the same source torus and still factors through that same
`R`, with ambient maximal splitness and centralizer `range (l' ≫ j)`.

The implemented proof takes the rational conjugating point and source
isomorphism from `SubgroupConjugate`. Naturality gives a conjugacy square
in `G`; the published range-square lemma and centralizer transport give
the centralizer equality. Maximal splitness is preserved by the ambient
inner isomorphism. The construction `conjugateFactor` retains the radical
factor as an actual morphism.

For a represented geometric solvable radical, its ground-field normality
and closedness supply the normality and representation premises. Applying
the result to rational Levis still requires a genuine rational Levi
conjugacy theorem and one genuine centralizer presentation. Neither is
proved or assumed to exist by this construction.
