# Character threshold regions from one ambient Weyl form

Author: Worker 200.

This internal adapter connects the constructed ambient form to the existing
actual-character threshold regions. It uses the full real character spaces
and the existing continuous unramified-character group with its canonical
rational-point topology. The local metric is constructed from one ambient
relative Weyl form through actual character restriction.

Let `f : A → T` be an actual morphism of split tori whose underlying scheme
map is monomorphic, and let `i : T.toGrp → G` be an actual monomorphism.
The actual relative Weyl quotient for `i` has an explicit `Fintype` instance.
The previously constructed `weylInducedCharacterForm hA hT f i` is positive
on every nonzero vector. Testing a vector against itself therefore proves
both separating conditions of `weylInducedCharacterForm_nondegenerate`.
No nondegeneracy or local-form comparison is assumed.

`weylInducedCharacterForm_root_inequality_iff` applies the proved compatibility
of the induced form and its orthogonal lift. For every actual character of
`T`, the ambient strict inequality at the lifted parameter is equivalent to
the local strict inequality at its actual restricted character. This
pointwise statement imposes no equality between ambient and local root sets.

In the character section the field is an arbitrary nonarchimedean local
field, in any universe and characteristic. The ambient group is affine.
The group `M` is affine and locally of finite type; its rational points carry
exactly `rationalPointTopology F M.X`.
For an actual map `j : A.toGrp → M`, two specified subgroup functors and a
real threshold, `weylUnramifiedIntertwiningRegion` specializes the existing
canonical continuous region. Its actual torus map into `G` is the composite
of `f` with `i`, and its metric is the induced ambient form.

Assume additionally that `G` is smooth, `M` is connected reductive, and `j`
satisfies the actual `IsSplitComponent` predicate. For any integral
cocharacters `nu`, `eta` of `A` and every real threshold, the dynamic region
contains a character obtained by applying the canonical continuous
image/unramified equivalence to `rationalImagePositiveCharacter M psi`
for some real additive functional `psi` on the actual valuation image.
The proof applies the existing positive-witness theorem using the
nondegeneracy just established. Its image-region membership is definitionally
the required canonical-region membership. The nonemptiness corollary retains
this explicit witness.

All actual relative roots in the two dynamic supports are tested, including
multipliable roots. The second dynamic group uses `-eta`. Empty indexing
sets, central directions and rank zero remain permitted. The provenance is
the proved ambient-form construction, its exact compatibility theorem, the
proved dynamic-region nonemptiness and positive-character extension, and
the existing canonical continuous equivalence.

Invariance of this same local form under a specified ambient normalizer point
preserving `f` is already proved by
`weylInducedCharacterForm_normalizer_invariant`; the actual commuting square
remains a hypothesis there. No arbitrary normalizer preservation, root-set
restriction identity, common-Levi or radical identification is inferred.
These threshold regions have not been proved to be convergence domains.
Finite length, intertwining convergence, rational continuation and
Plancherel remain separate obligations.
