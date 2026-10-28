# Strong endpoints from an actual common image

`Langlands.Classification.commonImageMultiplicityOne` proves exactly
`CommonImageMultiplicityOneStatement` with independent group, monoid,
smooth-carrier, functor-image-carrier and test-carrier universes. This is
an internal elementary argument; no printed theorem is attributed this
abstract formulation.

The proof uses `SmoothRep.image f`, the actual invariant range of the
given nonzero intertwiner, with its induced smooth action. The actual
range restriction `q` is surjective, its inclusion `j` into `B` is
injective, and `f = q ≫ j`. Thus `q` is nonzero. Source-quotient detection
gives a positive finite-series count for `F(image f)`. Preservation of
epimorphisms and surjective multiplicity monotonicity bound this count
by the count one on `F(A)`, so it equals one.

To prove image irreducibility, the implementation first shows that its
bottom and top invariant subrepresentations are distinct: otherwise the
range restriction, hence `f`, would vanish. For any invariant subobject
`S` which is neither bottom nor top, set `P = S` and `Q = image f / S`,
using the actual smooth subrepresentation and quotient constructions.
The inclusion of `P` into `B` is injective and nonzero because `S` is
nonzero. The composite quotient from `A` onto `Q` is surjective and
nonzero because `S` is proper. Target-subobject detection and
source-quotient detection therefore supply positive finite-series counts
for `F(P)` and `F(Q)`.

The private helper `positive_zero_composite_impossible` handles the
resulting contradiction. The inclusion `P -> image f` followed by the
quotient `image f -> Q` is zero. Functoriality and additivity preserve
this zero composite; mono/epi preservation makes the mapped inclusion
injective and the mapped quotient surjective. The mapped inclusion
factors injectively through the actual invariant kernel `K` of the
mapped quotient. `jordanHolderShortExactDecomposition` gives actual
finite-series counts on `K` and `F(Q)` summing to one. Injective
monotonicity bounds the positive count of `F(P)` by the count on `K`,
and multiplicity independence identifies the quotient count with the
already supplied positive count on `F(Q)`. Two positive natural counts
cannot sum to at most one. Every invariant subobject of the image is
therefore bottom or top, proving irreducibility including nonzeroness.

The published `multiplicityOneHeadCore` and `multiplicityOneSocleCore`
apply with this image as their supplied irreducible endpoint. Their
positivity hypotheses follow by restriction of the all-nonzero
detectors: an actual surjection onto an irreducible or injection from an
irreducible is nonzero. The small private
`irreducible_carrier_nontrivial` helper extracts nontriviality from the
nontrivial invariant-subobject lattice. The canonical head-kernel and
socle-image characterizations transfer the resulting strong constituent
relations to this same image object. Thus the result retains the given
factorization and equality of every irreducible quotient kernel and
every irreducible embedding image, not just isomorphism-class uniqueness.

No ambient finite-length theorem, prior simple-endpoint existence,
faithfulness, full-exactness hypothesis or test irreducibility is used.
The functor-image count assumptions include actual finite simple-series
witnesses. This abstract proof establishes no group-specific detector,
count, adjunction, induction map or segment classification conclusion.

The direct imports are `CommonImageMultiplicityOneStatement`,
`MultiplicityOneConstituentProof` and `MultiplicityAdditivityProof`.
Their recursive project import closure uses only category, smooth
subquotient/transfer, algebraic constituent and filtration machinery.
It is independent of segment, multisegment, tempered, square-integrable,
regular and analytic classification conclusions. The exact recursive
closure is recorded privately for the parent dependency audit.
