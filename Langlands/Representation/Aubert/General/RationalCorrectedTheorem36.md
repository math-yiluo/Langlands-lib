# Corrected Theorem 3.6 on the actual rational-point smooth category

`Langlands.Aubert.General.RationalPointFamily.RationalCorrectedTheorem36Statement`
is the corrected Theorem 3.6 target for a general connected reductive group over
a nonarchimedean local field. Its source is the official Aubert erratum (1996),
printed p.4687, display (*), with `Alg({I})` defined on that page and the
retained terminal cokernel explained on p.4690. The construction uses the
canonical maps of `RationalStandardComplex`, not only isomorphic degree objects.
This is a proposition definition, not a proof of the theorem.

The quantified field carries `IsNonarchimedeanLocalField`; no split or
quasisplit hypothesis is imposed on the group, no characteristic-zero
restriction is added, and the empty simple-root set is allowed. The torus is
an actual maximal split torus. The ambient group is literally
`RationalPoint k G.X` with the explicitly installed evaluation `pointTopology`.
Local compactness, nonarchimedean group structure and Hausdorffness of these
points are explicit intermediate topological inputs.

The subgroup families are literally the published standard parabolic, Levi
and unipotent point groups at `rootSet i ν I`, where `SimpleRoot i ν` is the
actual subtype of simple relative roots for the generic cocharacter. The
finite enumeration is derived from `HasRelativeRootSystem` and splitness
using `simpleRelativeRootFintype`. A linear order is universally quantified
to choose exterior coordinates. The named `StandardCocharacterStatement`,
`StandardParabolicOrderStatement`, `StandardParabolicEndpointsStatement`
and `StandardLeviIntersectionStatement` supply the decompositions, orders,
full-root endpoints and restricted inside-Levi decompositions through the
published adapters. Closedness of radicals and Levis and the radical
compact-limit property are explicit obligations. Unimodularity is derived
from the latter and is not a free normalization field.

The support predicate is the published `IsInSupportCategory`, with
`rootAssociation i ν hN hZ` substituted for the relation on root subsets.
Thus its irreducible subquotients have actual normalized cuspidal support,
with the same representative conjugating actual Levis and carrying the actual
simple-root subsets under the normalizer/full-centralizer character action.
`hN` and `hZ` are precisely the published scheme/point-image subgroup
comparisons. No arbitrary subgroup family, support relation or complex-data
structure is quantified in place of these definitions. The representation
universe is `max (u+1) v`, as in the published rational-point targets.

For every smooth input `E` in this support category, the target requires
`StandardComplex.IsExactBeforeTerminal`: its actual differential kernel equals
the preceding incoming image in every degree strictly below `|S|-|I|`.
There is no finite-length, irreducibility or admissibility premise on `E`.
The derived full-root endpoints identify the initial term with `E`. The final
cokernel is retained; there is no extra zero asserting that it vanishes.
`rationalTerminalProjection_surjective` and
`rationalTerminalProjection_ker` specialize the published intrinsic quotient
laws to the same actual families and canonical projection. These laws hold
without earlier exactness. They do not prove the theorem.

The theorem's proof must still supply the two-sided modified Bruhat supports,
double-coset minimality before using the geometric lemma, comparison of
consecutive modified supports and the actual surviving graded transition maps
up to exterior signs, as repaired in Ban–Jantzen (2016), Section 4, printed
pp.161–162. The filtration is finite in its Weyl index, not in the length of
the arbitrary smooth input. Proposition 3.2 remains unresolved; its original
proof and the original Theorem 3.6 proof do not supply this target. The named
intermediate topology, compact-limit, root and structural inputs must be
discharged or matched to the parent's itemized external structural list before
final parent closure. No representation-theoretic consequence has been moved
into that list, and no classification-independence claim is made.

The local topology instance is named `rationalCorrectedTheorem36PointTopology` to avoid
generated-name collisions when rational-family modules are imported together.
Its defining value remains `pointTopology`.
