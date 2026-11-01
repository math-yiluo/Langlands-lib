# Actual triple inner tensors

Authors: Worker 19; ordered-occurrence adapter reused from Worker 1216.

This internal adapter supplies actual inner tensors for a three-block
merge and either selected adjacent swap, including all outside singleton
blocks. It connects ordered coarse extraction to return after an actual
change in the selected block. It does not prove a local triple transfer.

The internal label permutation is the selected transposition on the
merged triple and the identity on each outside singleton. Its global
label formula proves compatibility with the existing global adjacent
swap. Permuting each actual inner block shape by this permutation gives
the target ordered refinement without changing any coarse rank.

The tensor factor comparison uses equality elimination on the actual
original family, retaining the rank casts in the ordered occurrence
adapter. The outside occurrence theorem reduces its inner permutation
to the identity and uses the original actual occurrence.

## Implemented interfaces

`BlockShape.tripleInnerSwap` is the transposition of inner slots `δ,δ+1`
when the coarse slot is `j`, for `δ ≤ 1`. It is the identity at every
other coarse slot. `tripleBlockEquiv_innerSwap` proves that its action on
the original consecutive labels is exactly the existing global adjacent
swap at `j+δ`. At the merged slot the proof expands both transpositions
and uses the explicit consecutive label formula. Outside it the inner
label has value zero and its global label lies outside the three selected
positions.

`triplePermutedRefinement` permutes each original inner shape by this
internal permutation. Its positive ranks and total rank come from the
existing `BlockShape.permute`. `triplePermuted_size` gives the exact
target global ranks, and `triplePermutedRefinement_eq_swap` identifies
it with the direct swapped refinement in `TripleMergeShape` by size
extensionality. Thus these are two presentations of the same actual
refinement over one common coarse shape.

`tripleInnerTensor` is the actual external tensor of the original factors
in each coarse block. `triplePermutedTensor` uses the internally permuted
labels. The original factors may be arbitrary smooth representations.
`triplePermutedTensorFactors_eq` proves that the latter is the exact
rank-transported target tensor in `orderedRefinementTensorFactors`.
Its private family-transport lemma uses equality elimination on the
original label equality; proof irrelevance identifies the displayed
rank-equality proofs. No carrier or representation is replaced by a
formal constituent label.

`triplePermutedOccurrence_of_ne` preserves an actual occurrence at any
outside slot. A private generic lemma first proves invariance of an
actual tensor Jacquet occurrence under a permutation equal to the
identity by equality elimination. Applying it to the actual inner
permutation avoids any change of the underlying subquotient relation.

`exists_tripleCoarseFactors` takes an admissible finite-length smooth
ambient representation `π`, an admissible irreducible family of original
factors `C`, and their whole external tensor as an actual subquotient of
the upper normalized Jacquet module at `B`. The bound `j+2 < B.length`
implies positive total rank by positivity of the block ranks. Ordered
extraction at `tripleMerge` and `tripleRefinement` then gives factors `X m`
which are irreducible, admissible and of finite composition length. Their
entire tensor is an actual subquotient of the coarse Jacquet module of
the same `π`. For every coarse block `m`, the actual original inner tensor
is an actual subquotient of its normalized Jacquet module. No
irreducibility of `π` is needed for this extraction.

`subquotient_tripleSwapJacquet_of_selected` takes that actual coarse
tensor occurrence and all original blockwise occurrences. Its additional
input is an actual permuted inner tensor occurrence in the Jacquet module
of the **selected** factor `X (tripleMergeIndex ...)` at the permuted inner
shape. It returns the actual tensor of the entire family
`fun i => C (B.adjacentSwap (j+δ) ... i)` in the normalized Jacquet module
of the same `π` at the exact correspondingly permuted shape.

The proof retains the supplied new occurrence in the selected block.
Every outside block uses `triplePermutedOccurrence_of_ne` and its original
occurrence. The exact tensor-factor equality and ordered return then
reassemble all blocks. This direction requires no irreducibility,
admissibility or finite-length hypothesis. The selected new occurrence is
a necessary input to this structural return theorem, not a result proved
by it. Establishing the two host local representation moves remains
additional work.

Field and carrier universes `uF,uV` remain independent, with every smooth
carrier in `Type uV`. The host uses the specialization of the carrier
universe to `max uF uV`. The supplied topology, upper normalized Jacquet
functors, existing actual `SmoothRep.IsSubquotient` relation, every
outside factor and every outside position are retained. There is no
distinctness, linkage, common-line, unitary or support restriction.

## Dependency audit

This is an internal specialization of actual tensor, finite-label and
ordered-occurrence constructions. Its direct imports are
`Group.GL.TripleMergeShape` and `Parabolic.OrderedTensorOccurrences`.
The ordered adapter is the unchanged construction by Worker 1216; the
other bundled prerequisites are by Worker 19. The generic
ordered-flattening proof identifies a lexicographically increasing
finite label bijection with the canonical flattened numbering by
uniqueness of a strictly increasing self-map of a finite ordinal.
Rank compatibility then identifies the literal original shape.
Substitution specializes the existing actual flattened extraction and
return. The induction module imported by that adapter supplies the
rank-aware tensor definition; no induction-transitivity proof from it
is used here.

Recursive traversal over Library base
`125fca1a70e8f89af98a36c8565617cd68f73be5`, with the bundled pending
prerequisites, contains 397 project modules including this entry. The
classification-named modules are exactly `CanonicalConstituents`,
`ConstituentRelations`, `CuspidalJacquetMultiplicityStatement`, `Essential`,
`FiniteLengthProof`, `FiniteLengthStatement`, `RelativeGenericityStatement`,
`RelativeJacquetMultiplicityStatement`, `RelativeRegularComparisonStatement`,
`Segments`, `Supercuspidal`, `SupercuspidalContragredientAux`,
`SupercuspidalContragredientStatement`, `SupercuspidalSupport`,
`SupercuspidalTwist`, `Tempered`, `TemperedInductionStatement`, and
`TemperedSupportStatement`.

The new used bodies are finite-label arithmetic, actual rank transport
by equality elimination, the supplied original occurrences, and the
two ordered occurrence theorems. Their lower proof routes were checked
in addition to the import inventory:

- `TripleMergeShape` uses positive finite rank sums, consecutive finite
  Sigma labels, exact block-coordinate order, actual adjacent
  transpositions and size extensionality. Its paired Markdown records
  the coordinate proof.
- Ordered extraction and return substitute the exact shape and label
  equalities into `FlattenedTensorOccurrences`. The tensor definition
  retains every original factor and its exact rank transport.
- The flattened bridge bundles the actual upper radical and
  inverse-half-modulus quotient comparison, and the finite dependent
  tensor regrouping. Its extraction uses an actual composition series
  and exact mapped-image filtration of the whole coarse Jacquet
  representation. Lower Jacquet finite length follows by
  proper-refinement rank induction with compact-coefficient
  quasicuspidal splitting. Admissibility of actual subquotients uses
  compact-open averaging and the presenting kernel sequence.
- Coarse tensor factorization uses compact averaging, a minimum
  fixed-space dimension, admissible Schur, Jacobson density and actual
  multiplicity-space evaluation. Refined block occurrence extraction
  uses the actual product-subgroup quotient tensor comparison and
  contraction in a trivially acted complementary tensor.
- Return tensors actual injective/surjective presentations, maps the
  coarse occurrence through the actual exact refined Jacquet functor,
  and uses the explicit normalized quotient-transitivity isomorphism.

These bodies are described in the paired ordered, flattened, coarse
extraction/factorization and tensor prerequisite files. They do not use
global support decomposition, general ordered quotient coverage,
multisegment classification or any conclusion of the eight
classification tasks excluded by the host contract, including their
proof successors. This unit proves the ambient structural reduction
only; it supplies neither local repeated-factor rank-three structure
nor the host's exact final conjunction.
