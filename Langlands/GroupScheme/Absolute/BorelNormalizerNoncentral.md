# The noncentral branch with a canonical centralizer

Author: Worker 1446.

This internal deduction combines the published affine dynamic representatives,
dynamic smoothness and connectedness, the actual-intersection Borel adapter,
and the proper-centralizer Lie-dimension induction step. The two membership
helpers retain `CentralizerBorelIntersectionStatement` as an explicit hypothesis.
The point-selection entry supplies the published proof
`centralizerBorelIntersection` internally. The smaller-group induction
hypothesis remains explicit, so this construction does not prove the complete
`BorelNormalizerStatement`.

Work over an algebraically closed field in arbitrary universe `u`, with a
smooth connected affine group scheme `G` and a Borel inclusion `b : B ⟶ G`.
Suppose a cocharacter `χ` has its full range in `b` and is noncentral.
`mem_borelRange_of_noncentral_cocharacter` constructs
`Dynamic.Affine.centralizerScheme χ` and its canonical closed inclusion into
`G`. The published representative theorem identifies its all-test point
functor with `Dynamic.centralizer χ`. The published dynamic theorems supply
smoothness and connectedness of this representative.

The intersection adapter applies the assumed exact
`CentralizerBorelIntersectionStatement` and proves that the actual first
projection from the pullback of this inclusion with `b` is Borel in the
centralizer. Noncentrality makes the centralizer inclusion nonisomorphic.
The existing proper-centralizer induction step then applies the given
normalizer hypothesis for all smaller smooth connected affine groups, using
strict decrease of Lie dimension. It places every ground-field point that
normalizes the image of `B(k)` and belongs to the dynamic centralizer in the
image of `B(k)`.

`mem_borelRange_of_noncentral_commutatorKernel_of_intersectionStatement`
specializes this result to a monic map `i : T.toGrp ⟶ G` from a commutative
group scheme whose full range lies in `b`. For `n : normalizerPoints i` and
an actual cocharacter `ν` killed by `torusCommutatorEnd i n`, the published
commutator equivalence places the original point `n.val` in the centralizer
of `groupHom ν ≫ i`. The range of this composite lies in the range of `i`,
hence in `b`. If the composite is noncentral and `n.val` also normalizes
the image of `B(k)`, the first theorem applies. The argument requires no
torus predicate on `T` and no closedness or nontriviality premise on `ν`.

`borelPointOfNoncentralKernel` applies the commutator-kernel membership helper
to the published `centralizerBorelIntersection` proof, then uses classical
choice on the resulting range membership. It has no intersection-statement
parameter. Its value is an actual ground-field point `p` of `B` with the
retained equality `p ≫ b.hom.hom = n.val`. The conditional membership helpers
keep their existing signatures for consumers that supply an intersection
proof explicitly.

No centralizer representative, connectedness witness or Borel-intersection
witness is supplied by the point-selection consumer. The smaller-group
induction hypothesis, containment, normalization, commutator-kernel and
noncentrality inputs remain explicit. The construction asserts no existence
of such a kernel cocharacter and does not handle the central-cocharacter or surjective
commutator branches. Its provenance is the stated composition of published
Library results, with no additional external-source claim.
