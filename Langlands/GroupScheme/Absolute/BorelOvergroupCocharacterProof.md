# Actual integral cocharacters of absolute Borel overgroups

Worker 146 assembled this proof with Worker 1272's integral averaging and root
support recognition implementations. Worker 1240 contributed the recognition
outline used in the latter.

`Langlands.GroupScheme.absoluteBorelOvergroupCocharacter.{u}` proves exactly the
unchanged published proposition
`Langlands.GroupScheme.AbsoluteBorelOvergroupCocharacterStatement.{u}`.
For every algebraically closed field `k : Type u`, a connected reductive group
`G`, a specified split torus `T` and map `j : T.toGrp ⟶ G`, a smooth closed
subgroup `i : P ⟶ G`, and an actual map `b : B ⟶ P` satisfying
`IsBorelPair (b ≫ i) j`, it produces an actual integral cocharacter
`ζ : cocharacterLattice T`. The image subgroup of `P(k)` equals the field
points of `Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ j)`.
Connectedness of `P` is derived, with no additional premise.

The implementation proves equality of subgroup functors on every test scheme
before evaluating at the identity object over `Spec k`. It uses an integral
finite orbit sum and actual tangent support, rather than the simple-root
classification route described in the statement's source discussion. The
construction and recognition steps are internal deductions from the proved
Library results detailed below.

The helper `exists_regularCocharacter_positiveRoots_supported` applies
`regularCocharacterBorel` to the specified Borel pair and its actual torus
factorization. The connected reductive ambient group supplies smoothness and
affineness. The result gives a regular integral cocharacter `ν` of this same
torus whose dynamic parabolic is represented by the specified Borel.
`SubgroupFunctor.range_comp_le` puts this dynamic parabolic in the overgroup.
The proved `dynamicLie` formula and the split-torus weight decomposition
identify its Lie image with the span of the weights having nonnegative
pairing with `ν`. The support criterion for that span and support monotonicity
then put every actual positive root into
`S = RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation j)
(SubgroupFunctor.range i)`. This helper works over any field and does not
require connectedness of the overgroup.

The helper `exists_regularCocharacter_support_and_inverters` additionally uses
the algebraic closedness of the field and the actual Borel factorization.
`borelContainingSubgroupConnectedStatement` proves `P` connected, and the
factorization of `j` through `B` gives an actual torus lift into `P`.
The proved `exists_supportPreserving_weylInverter_of_both_signs` then applies
to this smooth connected closed overgroup and the specified split maximal
torus. For every actual root `α` with both `α` and `-α` in `S`, it supplies
an element of the actual `relativeWeylGroup j` that sends `α` to `-α` and
preserves membership in `S` for every character.

That inversion input is proved in the accompanying modules using the generic
rank-one cocharacter centralizer. One-dimensional root Lie spaces, root
reducedness, and maximal-torus self-centralization put its entire tangent
image in that of `P`. The intersection with `P` is represented as an internal
cocharacter centralizer; dynamic smoothness and connectedness therefore
justify the included-subgroup full-Lie comparison proving containment.
The proved rank-one nonidentity-normalizer and negation results supply an
actual normalizer point in this contained centralizer. Its conjugation
preserves the entire tangent support, and the actual Weyl quotient inherits
this action. Thus the inversion input is a proved geometric conclusion,
not an additional classification premise.

The final theorem applies
`exists_cocharacter_of_rootSupport_negators` to this `S`, the regular `ν`
(equivalently generic), the positive-root inclusion, and the supplied
inverters restricted to actual roots. Its structural inputs are the proved
finiteness of the actual Weyl group for a split maximal torus in a connected
reductive group and the proved root-negation theorem. It forms the subgroup
`H` preserving `S` on actual roots and takes the integral sum
`ζ = ∑ w : H, relativeWeylCocharacterAction j w.val ν`.
No division or rational lift is needed. The sum is `H`-fixed. An absent root
pairs strictly negatively with every summand. A root with both signs present
pairs to zero because its support-preserving inverter fixes `ζ`. A present
root whose negative is absent pairs strictly positively. Consequently every
actual root satisfies `α ∈ S ↔ 0 ≤ latticePairing T α ζ`.

The proved
`borelOvergroup_eq_dynamicParabolic_of_rootSupport` recognizes the actual
overgroup from this equivalence. Its hypotheses are precisely the original
smooth closed Borel factorization, connected reductive ambient group, split
torus, and supplied root-support equivalence; it derives connectedness and
torus containment. Zero weight is handled separately by maximal-torus
self-centralization. One-dimensional root spaces and the stable weight
decomposition identify the full tangent image. The proved dynamic semigroup
containment gives inclusion in the dynamic parabolic. Dynamic closed
representability, smoothness, connectedness and the Lie formula then allow
the included-subgroup full-Lie comparison to give equality on every test
scheme. Evaluating its carrier at `Over.mk (𝟙 (Spec (CommRingCat.of k)))`
gives exactly the target's field-point equality.

The theorem retains the original universe, every characteristic and general
connected reductive groups, including central tori. There is no nonempty-root,
positive-rank, proper-overgroup or nonzero-output assumption. The stabilizer
subgroup always contains the identity; when the root system is empty, the
root conditions are vacuous and the recognition argument still handles the
zero weight. The full ambient overgroup is included.
The proof uses neither `SplitParabolicCocharacterStatement` nor
`ParabolicDynamicStatement`, nor the parabolic-intersection geometry chain
that consumes them. The published target and all pairs it imports are
unchanged.
