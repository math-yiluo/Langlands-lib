# The actual PQ regularity quotient and its filtered kernel criterion

Author: Worker 154. Module
`Langlands.Representation.Intertwining.PQRegularityFiltration`.

This derived module constructs the actual natural quotient appearing in
`pqRegularityKernel` and connects its finite filtrations to the published
kernel and spectral criteria. The filtration, its natural grade
identifications, and the finite action-algebra hypotheses used for the
spectral converse are explicit premises. This is an intermediate result for
Task 5300; it does not prove `PQRegularityLemmaStatement` or
`PQSupportGradedStatement`.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version
of 9 July 2026, VII.3.3, Lemma and proof, printed pp.234–235 / PDF pp.240–241.
Registered source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 154 read both pages again while implementing this module.

The provenance is derived. Renard chooses a total refinement placing the
strict Bruhat predecessors of the identity before it, filters the quotient
by their geometric pieces, and compares its annihilator with the
intersection of their annihilators. He then uses generalized exponents and,
for the converse, finite-length annihilator bounds. Here the natural quotient
and filtered kernel calculations are actual constructions from existing
Library interfaces. The converse uses the alternative finite action-algebra
criterion of `PQFiniteActionRegularity`; its hypotheses have not been deduced
from the finite-length premise in Renard's Lemma.

## Quotient and filtration

For arbitrary represented source and target parabolic triples with the same
underlying Levi scheme `M`, `pqRegularityQuotientFunctor` is the smooth
ambient quotient by `boundarySupportImage` at the identity double coset,
followed by forgetting smoothness. Its object at `σ` is definitionally the
quotient representation whose group-algebra kernel is `pqRegularityKernel`.
The two embeddings of `M` into the ambient group need not be equal for these
algebraic constructions. The field and coefficient-carrier universes remain
independent.

`pqRegularityProjection` is the actual quotient-class map, natural in `σ`.
`pqRegularityProjection_mem_kernel` and
`pqRegularityProjection_surjective` identify its exact kernel and prove
surjectivity.

Given an ordered double-coset support flag of length `a + b` and an equality
identifying its step `a` with the boundary image at every `σ`,
`pqRegularitySupportFiltration` applies the published `quotientTail`
construction. Its steps are the actual images of the surviving support
steps under the quotient projection. It starts at zero and ends at the
whole regularity quotient. `pqRegularitySupportGradedIso` retains each
original grade at index `a + i` by the published direct-image quotient
comparison. The boundary-step equality and the ordered double-coset flag
are supplied data, not existence conclusions of this module.

## Kernel and spectral criteria

`groupAlgebraKernel_eq_of_equiv` proves that an equivariant equivalence
preserves the kernel of the same group-algebra action. The proof extends
intertwining from group elements by finite-support linear induction and
uses surjectivity in both directions. Natural identifications of a
filtration's grades therefore identify the intersection of their action
kernels; `PQFilteredKernels.gradedKernel_eq_pieceKernels` and
`sup_kernel_eq_top_iff_pieceKernels` express this comparison.

For any supplied finite filtration of the actual regularity quotient and
natural isomorphisms of all its grades with a finite family `pieces`,
`pqRegularity_iff_pieceKernels` proves that `IsPQRegular` is equivalent to
comaximality of `splitComponentKernel` with the intersection of the piece
kernels. `pqRegularity_iff_all_pieceKernels` equivalently tests comaximality
against each piece separately. It uses the finite-family comaximal-ideal
lemma, including the empty family.

`pqRegularity_disjoint_generalizedCharacters` applies the published
finiteness-free kernel containment argument to each piece.
`pqRegularity_of_disjoint_generalizedCharacters` proves the converse when
the action quotient of `σ` and that of each supplied piece, restricted to
the same group of split-component points, are finite-dimensional over `ℂ`.
No finiteness of the representation carriers is assumed.

For a split component `a` and smooth piece models,
`pqRegularity_disjoint_weights` and `pqRegularity_of_disjoint_weights`
express these implications using exactly the published `groupExponents`
and `IsGeneralizedWeight` predicates. The canonical Levi topology supplies
local compactness and a nonarchimedean group structure; the actual scheme
point map is continuous. The existing `isGeneralizedWeight_iff` therefore
identifies these compact-open weights with algebraic generalized
characters. It also supplies openness of the character kernels; that
openness is not a new premise. The converse retains the same explicit
finite action-quotient assumptions.

## Remaining exact-target obligations

The exact VII.3.3 application must still construct the quotient filtration
whose grades are all and only the prescribed strict Bruhat predecessors
of the identity, identify them naturally with the original
`GeometricLemmaIntersectionDatum.pieceFunctor` values with the same action,
and prove that finite length of `σ` implies the required finite action
algebras. Smoothness of a supplied arbitrary `pieces` family is explicit
in the weight formulations. For the original geometric pieces it is a
property of their construction from smooth functors.

The imports reuse `PQFilteredKernels`, `PQFiniteActionRegularity`,
`ArbitraryParabolicInduction`, `Category.NaturalCokernel`, and
`Filtration.QuotientTail`. The original target statements and their import
closure are unchanged.
