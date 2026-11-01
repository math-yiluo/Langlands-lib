# Adjacent cuspidal Jacquet interchange

Authors: Worker 1216, with Worker 19's coarse extraction and tensor occurrence
adapters and Worker 289's adjacent binary induction bridge.

`Langlands.Classification.adjacentCuspidalJacquetInterchange` proves exactly
the published proposition
`Langlands.Classification.AdjacentCuspidalJacquetInterchange.{uF,uV} F T`
from
`Langlands.Representation.Classification.AdjacentCuspidalJacquetInterchangeStatement`.
Its only parameters are
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The universes `uF` and `uV` are independent. The statement's Lean/Markdown
pair and all imported Library pairs are unchanged.

## Scope and conventions

For an irreducible admissible finite-length actual smooth representation
`π` of `GL_n(F)` and a family `A` of actual supercuspidal block objects,
start with the stipulated actual subquotient of the normalized upper
Jacquet module at `B`. The pair at positions `j,j+1` has irreducible
binary normalized product and the supplied actual isomorphism to the
reversed binary product with the literal
`Derivative.generalLinearRankCast T (Nat.add_comm (B.size b) (B.size a))`.
The conclusion is the actual subquotient of the Jacquet module at
`B.permute (B.adjacentSwap j hj)` with factors
`fun i => (A (B.adjacentSwap j hj i)).obj`.

Every occurrence is `SmoothRep.IsSubquotient`, the existing relation
presented by an actual invariant subspace, an actual quotient, and an
isomorphism. The proof uses no identity of virtual classes or
semisimplifications as a replacement for that relation. It assumes no
whole-product embedding and no quotient of the whole original Jacquet
module. All outside factors remain present, including repetitions; there
is no ordering, distinctness, regularity or support premise.

The installed topology is `T.topology`. The normalized upper Jacquet
action uses inverse half-modulus, and normalized induction uses positive
half-modulus covariance and right translation, as in the statement.
The original carriers lie in `Type (max uF uV)`; the generic extraction
interfaces are specialized to that carrier universe. Applying normalized
induction therefore stays in the same universe. A chosen adjacent pair
implies positive total rank by `B.length_le`. For ranks and shapes without
such a pair, the quantified implication needs no separate construction.
The assembly does not use the given irreducibility of `π`; it retains the
exact published statement, including that premise.

## Implemented proof

Write `C = B.adjacentMerge j hj`, `S = B.adjacentRefinement j hj`,
`R = B.adjacentReverseRefinement j hj`, and `σ = B.adjacentSwap j hj`.
The shape `C` keeps every outside block and merges only the chosen pair.
The shape `S m` has two blocks at the merged slot and one elsewhere;
`R m` reverses those inner blocks.

1. Apply `Parabolic.exists_factorized_coarseJacquet_of_ordered` with the
   actual increasing label equivalence `B.adjacentBlockEquiv j hj`,
   `adjacentBlock_size`, and `adjacentBlockEquiv_lt_iff`. This returns
   actual coarse factors `X m`, all irreducible, admissible and of finite
   length, together with
   `externalSmoothObject X` as an actual subquotient of `r_C π`.
   For every `m`, the actual `adjacentInnerTensor ... m`, denoted `D m`,
   is an actual subquotient of `r_(S m) (X m)`.
   Here the ordered tensor family is definitionally `D`. Positivity,
   admissibility and finite length discharge the extraction hypotheses;
   irreducibility and admissibility of each original factor are provided
   by its supercuspidal subtype.
2. `adjacentInnerTensors_cuspidal` makes `D m` irreducible and
   Levi-cuspidal and makes the actual reversed tensor `E m` irreducible.
   `adjacentInnerInductions_irreducible_iso` uses exactly the two supplied
   binary hypotheses to prove that `i_(S m) (D m)` is irreducible and is
   actually isomorphic to `i_(R m) (E m)`, for every coarse slot.
3. Apply `cuspidalOccurrence_transfer_of_inductionIso` to `X m,D m,E m`.
   Normalized Jacquet admissibility and
   `leviCuspidalConstituentTheorem` upgrade the local cuspidal occurrence
   to an actual surjection `r_(S m) (X m) → D m`.
   The concrete normalized first adjointness equivalence turns it into
   a nonzero map `X m → i_(S m) (D m)`. Irreducibility of source and
   target makes this an actual isomorphism. Compose with the isomorphism
   from step 2 and use nonzero Jacquet evaluation at the identity.
   Irreducibility of `E m` makes that evaluation surjective, proving an
   actual quotient, hence an actual subquotient,
   `E m` of `r_(R m) (X m)`. These are proved quotients of the extracted
   local Jacquet modules, not strengthened input assumptions.
4. Apply `subquotient_orderedJacquet_of_coarse_factors` to the same
   whole coarse occurrence, the refinement `R`, and the target factors
   `fun i => (A (σ i)).obj`. Its size law is `adjacentReverse_size`;
   its order law is again `adjacentBlockEquiv_lt_iff`.
   Rewrite its inner tensor family by `adjacentReverseTensorFactors_eq`
   and supply step 3. This tensors the actual local subquotient
   presentations, preserves the actual coarse occurrence through the
   exact refined Jacquet functor, and applies normalized transitivity
   and the ordered flattened comparison to produce the exact conclusion.

## The extraction and tensor dependencies

The ordered-label adapter first proves that an increasing bijection from
outer/inner block pairs to fine labels is the canonical consecutive
numbering. A strictly increasing self-map of a finite ordinal is the
identity. The size identities then prove equality of actual block shapes,
not just equality of their numbers of blocks. Substitution reduces its
two occurrence lemmas to the flattened occurrence interfaces. Rank
equality transports agree by equality elimination and proof irrelevance.

`Parabolic.exists_factorized_coarseJacquet_of_flattened`
uses admissible scalar Schur and finite tensor irreducibility to make
the entire original fine tensor irreducible. The actual standard
flattened Jacquet comparison carries it to the composed Jacquet module.
`CoarseJacquetExtraction.exists_irreducible_coarseJacquet_subquotient`
uses a composition series of the finite-length coarse Jacquet object.
`ExactConstituentExtraction` constructs the actual image filtration
under the refined functor. Its exact graded comparison and
`ActualGradedExtraction` put the given irreducible actual subquotient
in the image of one irreducible coarse grade. Each grade itself is an
actual quotient of a subrepresentation. This supplies the needed
coarse constituent without assuming that the input occurrence splits.

Admissibility passes to that actual constituent using an
injective/surjective presentation and compact open averaging in its
kernel sequence. `padicLeviAdmissibleFactorization` realizes it as an
actual external tensor of irreducible admissible coarse factors. This
is finite induction using the two-factor existence theorem: compact
averaging and minimum fixed-space dimension produce a simple first
factor; scalar Schur and Jacobson density make multiplicity-space
evaluation bijective; evaluation also gives admissibility and
irreducibility of the other factor. It uses no supercuspidal-support
existence or uniqueness conclusion. Simplicity supplies each factor's
finite length.

The blockwise occurrences then follow from the actual refined tensor
Jacquet isomorphism and `Tensor.SmoothSubquotients` factor extraction.
The quotient comparison tensors actual quotient projections; its inverse
descends the pure-tensor map through each relation submodule. Product
modulus identities give upper normalized equivariance. To extract one
factor of an actual tensor subquotient, restrict to its coordinate,
so the complementary tensor has trivial action. Contract that tensor
on a finite support of minimum nonzero dimension. Minimality puts the
contraction kernel in the presenting quotient kernel; descent and
irreducibility yield a genuine subquotient of the selected ambient
factor. Conversely, tensoring actual injective/surjective spans gives
the return occurrence; linear retractions and sections prove tensor
injectivity and surjectivity. Every factor is retained in both directions.

Detailed implemented arguments and their dependency audits are in
[CoarseJacquetExtraction.md](../Filtration/CoarseJacquetExtraction.md),
[CoarseJacquetFactorization.md](../Filtration/CoarseJacquetFactorization.md),
[SmoothSubquotients.md](../Tensor/SmoothSubquotients.md),
[RefinedTensorOccurrences.md](../Parabolic/RefinedTensorOccurrences.md),
[FlattenedTensorOccurrences.md](../Parabolic/FlattenedTensorOccurrences.md)
and [OrderedTensorOccurrences.md](../Parabolic/OrderedTensorOccurrences.md).

## Local induction and literal rank transport

The [binary bridge](../CuspidalSupport/AdjacentInnerBinaryBridge.md)
reconstructs the actual positive two-block shape from its size laws.
Equality elimination identifies its product induction with the binary
product cast to the total rank. At the merged slot its two dependent
labels are exactly `j,j+1`. Mapping the supplied isomorphism through
the total-rank cast composes that cast with the literal `Nat.add_comm`
cast. `generalLinearRankCast_trans` proves that this is the reversed
shape's total-rank cast. No block permutation silently replaces that
cast. At every other slot reversal fixes the sole label, and the proved
single-block induction lemma supplies irreducibility through surjective
group maps, character twist and the actual full-group induction
equivalence. No general associated-induction matching theorem is used.

The [local occurrence helper](../CuspidalSupport/IrreducibleInductionOccurrence.md)
uses the published cuspidal constituent theorem, actual normalized
Jacquet admissibility, concrete first adjointness and evaluation, and
the elementary fact that a nonzero intertwiner between irreducibles is
bijective. Its output is an actual smooth isomorphism, followed by the
actual reversed Jacquet quotient used above. The inner tensor
irreducibility and cuspidality come from `glCuspidalTensor`, with
admissible scalar Schur, tensor irreducibility and vanishing of proper
block Jacquet modules. The unused induction-in-stages comparisons in
`AdjacentMergedTensor` do not supply an extra premise.

## Import and mathematical independence audit

At Library base `8d926c3850083c700afa54adc0d07240e27fe799`, recursive
resolution of the four direct imports, including this entry and all
eight new supporting modules, gives 440 project modules and 180 distinct
direct external imports across their closure. All project imports
resolve. Every Lean file has a nonempty Markdown companion. Byte
comparison with that Library base finds no changed imported Library
Lean/Markdown pair.

The four direct imports are the exact statement,
`Parabolic.OrderedTensorOccurrences`,
`CuspidalSupport.IrreducibleInductionOccurrence`, and
`CuspidalSupport.AdjacentInnerBinaryBridge`, all under
`Langlands.Representation`.
The complete classification-module inventory, besides this entry and
its target, is `CanonicalConstituents`, `ConstituentRelations`,
`CuspidalJacquetMultiplicityStatement`, `Essential`, `FiniteLengthProof`,
`FiniteLengthStatement`, `RelativeGenericityStatement`,
`RelativeJacquetMultiplicityStatement`, `RelativeRegularComparisonStatement`,
`Segments`, `Supercuspidal`, `SupercuspidalContragredientAux`,
`SupercuspidalContragredientStatement`, `SupercuspidalSupport`,
`SupercuspidalTwist`, `Tempered`, `TemperedInductionStatement`, and
`TemperedSupportStatement`. These supply definitions, statement
interfaces, elementary transports and the lower finite-length proof;
none supplies an excluded classification conclusion.

The nontrivial lower proof routes were checked in addition to this
import inventory:

- `normalizedJacquetFiniteLength` in `Classification.FiniteLengthProof`
  inducts on `n - C.length`. Admissibility follows from canonical
  stable-image lifts and small block Iwahori subgroups. Finite generation
  comes from finitely many ambient generators and the compact parabolic
  quotient. Quasicuspidal finite length comes from compact-coefficient
  semisimplicity on the determinant-unit subgroup and a finite
  fixed-vector generating space. Splitting off that part uses the
  natural compact-coefficient projector. Its analytic inputs are
  discharged by determinant-unit isotypic complements, finite fixed-level
  strata, compactness and exhaustion, and the Harish-Chandra criterion
  proved by Cartan support, contraction and averaging. The complement's
  strict chains are bounded by lengths of proper refined Jacquet
  modules; flattened quotient surjectivity and the smaller measure close
  the induction. This quasicuspidal splitting is not a decomposition by
  global supercuspidal supports.
- Actual refined exactness uses smooth averaging and compact containment
  of the refined radical to prove coinvariant injectivity, together
  with the quotient range-kernel and surjectivity laws. Transitivity
  descends quotient maps through the two radicals and constructs the
  inverse by their factorization. Inverse half-moduli multiply correctly.
  The flattened comparison checks the same radical and Levi embeddings
  on matrix entries; its modulus calculation separates determinant
  products into pairs in the same and different outer blocks.
- The cuspidal constituent theorem is used for its actual quotient
  conclusion. Its lower cuspidal-support route includes the
  maximal-block-count proof of `minimalNonzeroJacquet`, bounded by total
  rank and the surjection to iterated coinvariants. It is independent
  of segment and multisegment classification. The tensor and
  factorization routes are the actual module constructions described
  above, rather than support-label comparisons.

The closure contains none of the following excluded conclusions, their
closing theorem names, or their named proof successors; the implemented
proof dependencies described above also do not invoke them:

| Excluded task | Excluded conclusion |
| --- | --- |
| `aca8805b-054f-4d56-8045-12db7f623404` | Analytic segment classification, `SegmentEssentialSquareIntegrableClassification` |
| `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` | Multisegment exhaustion, `MultisegmentHeadExhaustion` |
| `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | Ordered strong-head existence, `OrderedMultisegmentHeadExistence` |
| `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` | Ordered quotient coverage, `OrderedMultisegmentQuotientExhaustion` |
| `52e97845-36bb-457d-b76f-70753334b88c` | Tempered block uniqueness, `TemperedBlockUniqueness` |
| `1cb45da2-7007-4351-a694-594fb148b8d1` | `SquareIntegrableLanglandsClassification` |
| `cd8ab97c-0b78-4bce-97c4-d307a28159a4` | `SquareIntegrableLanglandsExhaustion` |
| `bf433f0a-921a-428c-b0c0-6475438125ac` | Regular exhaustion, `GLRegularLanglandsExhaustionStatement` |

In particular, no full disjoint-support decomposition, general ordered
quotient coverage or multisegment classification is used as a shortcut.
The local pair hypotheses are the only commutation and irreducibility
premises beyond the published ambient and factor data.

## Provenance and checking

This is a derived proof of the existing Library statement. Its
[paired statement documentation](AdjacentCuspidalJacquetInterchangeStatement.md)
records the source comparison: Jantzen 1997, Lemma 5.4 and Section 10,
and Jantzen 2000, Lemma 2.1.2. No original is claimed to state this
precise actual-object proposition verbatim. The implemented proof follows
the local fusion and reversed refinement mechanism, with actual
composition-series extraction and actual quotient maps supplying the
steps that the source presents through constituent multiplicities.
The sources' global decomposition and classification conclusions are
not inputs.

Development compilation and declaration inspection succeed in approved
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with independent
`uF,uV` and only `propext`, `Classical.choice` and `Quot.sound`.
Development checking is not independent semantic acceptance,
exact-target submission validation or Library publication.
