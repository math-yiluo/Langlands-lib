# The commutator-kernel proper-centralizer branch

This internal helper connects the actual torus commutator endomorphism to the
existing Lie-dimension induction step. It is an intermediate deduction for the
Borel normalizer proof.

Over any base scheme, if a homomorphism `j : M ⟶ G` represents the dynamic
centralizer of an actual cocharacter `χ` and `j` is an isomorphism, every test
point of `G` lifts through its inverse. Therefore the represented centralizer
is the full subgroup functor. The existing
`isCentral_iff_dynamicCentralizer_eq_top` makes `χ` central on all test schemes.
The contrapositive says that a noncentral cocharacter has no isomorphic
centralizer representative. This argument requires no closedness or geometric
hypotheses on the base or groups.

The field specialization works over an arbitrary field. Let `G` be smooth, connected
and affine; let `n` normalize an actual monic commutative-group-scheme map
`i : T.toGrp ⟶ G`; and let a cocharacter `ν` satisfy
`ν ≫ torusCommutatorEnd i n = 0`. The commutator helper proves that the original
point `n` belongs to the dynamic centralizer of `groupHom ν ≫ i`. If that
ambient cocharacter is noncentral, the preceding contrapositive proves that
every representative `j` of this centralizer is not an isomorphism.

Assume that `j` is a closed representative with connected source, that its
actual pullback intersection with `b : B ⟶ G` is Borel in its source, and that
the original point normalizes the ground-field point image of `b`. The
existing proper-cocharacter-centralizer induction theorem then puts `n` in
that image, using the supplied Borel normalizer hypothesis for every smaller
smooth connected affine group. That theorem supplies smoothness of the
centralizer and affineness of its closed source before applying strict
Lie-dimension decrease.

`borelPointOfNoncentralCommutatorKernel` chooses an actual ground-field point
of `B` from this range membership, together with its equality after
postcomposition with `b` to the original point `n`. It has exactly the same
hypotheses as the membership theorem.

The connectedness and Borel-intersection premises, a centralizer
representative, the noncentral kernel cocharacter, and the smaller-group
induction hypothesis are explicit inputs. In particular this helper does not
assert their existence or prove the complete `BorelNormalizerStatement`.
