# Rank-one self-association from a normalizing Weyl element

Author: Worker 63.

This internal supporting unit restates the representation-theoretic content of
the published `RationalRankOneSelfAssociationStatement` in normalizer form and
proves that the two forms are equivalent at the full rational scope. The
normalizer form asks for one actual rational point. It must normalize the torus
point image and the maximal standard Levi `L_J`, and it must lie outside `L_J`.
The unit proves neither form. The implication from reducible cuspidal
induction to such a point is still open.

## Pure Coxeter step

The declarations in this section belong to
`Langlands.Group.RelativeWeylIndexing`. Take any Coxeter system
`cs : CoxeterSystem M W`, with finite index type `B`, decidable equality on
`B` and finite `W`. Fix a maximal proper subset `J = univ.erase α`.

`associatedSubset_eq_of_normalizes_of_not_mem` assumes `w ∉ W_J` and
`w * x * w⁻¹ ∈ W_J` for every `x ∈ W_J`. It proves
`associatedSubset cs J = J`. The proof has these steps.

1. Let `d = a * w * b` be a least-length element of the double coset
   `W_J w W_J`, given by `exists_minimal_in_doubleCoset`. Then `d` still
   normalizes `W_J`, and `d ∉ W_J`; in particular `d⁻¹ ≠ 1`.
2. Conjugation by `d` maps the finite set `W_J` injectively into itself, so
   by `Finset.surjOn_of_injOn_of_card_le` it is onto. Hence `d⁻¹ s_i d ∈ W_J`
   for every `i ∈ J`.
3. `isMinimal_inv` makes `d⁻¹` minimal in `W_J d⁻¹ W_J`. The published
   `exists_conj_simple_eq_of_isMinimal` turns each conjugate from step 2 into
   a simple reflection indexed by `J`. This gives
   `MapsIntoSimple cs d⁻¹ J J`.
4. Restricting the right factor to `W_∅ = ⊥` shows that `d⁻¹` is minimal in
   `W_J d⁻¹`. By `minimalityLengthCriterion_proof`, every index of `J` is a
   right ascent of `d⁻¹`. Since `d⁻¹ ≠ 1`, it has a right descent
   (`CoxeterSystem.exists_rightDescent_of_ne_one`). Because `J` omits only
   `α`, the set `positiveSimpleSet cs d⁻¹` equals `J`.
5. `longestSurvivor_proof` now identifies `d⁻¹` with `longestRep cs J`. So
   `associatedSubset cs J = simpleImage cs d J`.
6. If `d s_i d⁻¹ = s_j` with `i ∈ J`, then `s_j ∈ W_J`, so `j ∈ J`
   (`mem_of_simple_mem_standardSubgroup`). Conversely, step 3 writes every
   `j ∈ J` as such an image. Hence `simpleImage cs d J = J`.

`longestRep_not_mem_standardSubgroup` proves `longestRep cs J ∉ W_J` for the
same `J`. If it lay in `W_J`, its minimality in `W_J · longestRep cs J`
compared with `1` would force length zero. Then every member of `D(J,∅)` would
be `1` by `length_le_longestRep`. The minimal member of `W_J s_α` would
therefore be `1`, which puts `s_α` in `W_J`. That contradicts `α ∉ J`.

## The actual normalizer quotient

Here `T : Subgroup G` and `L : Finset B → Subgroup G` are arbitrary. The
quotient `RelativeWeyl.Weyl T` is the actual normalizer modulo the full
centralizer. `actual` is a Coxeter system on that quotient, and
`actualLeviWeylIdentification T L actual` says that the image of each actual
Levi Weyl quotient `N_G(T) ⊓ L I` modulo `Z_G(T)` is `standardSubgroup actual I`.

`associatedSubset_eq_of_normalizing_point` takes this identification, a
maximal proper `J`, the containment `Z_G(T) ≤ L J`, and
`n : RelativeWeyl.normalizer T` with `n x n⁻¹ ∈ L J` for `x ∈ L J` and
`n ∉ L J`. It proves `associatedSubset actual J = J` by applying the Coxeter
step to the class of `n`.

- If the class of `n` were in `W_J`, it would equal the class of some
  `y ∈ N_G(T) ⊓ L J`. Then `y⁻¹ n ∈ Z_G(T) ≤ L J`, hence `n ∈ L J`.
- For a class `[y]` with `y ∈ N_G(T) ⊓ L J`, the point `n y n⁻¹` again lies in
  `N_G(T) ⊓ L J`, and its class is `[n][y][n]⁻¹`.

`longestLift_not_mem` proves that no lift `n` of `longestRep actual J` lies in
`L J`. Otherwise its class would lie in `standardSubgroup actual J`, which
contradicts `longestRep_not_mem_standardSubgroup`.

## Generic rank-one predicates

In `Langlands.Aubert.General`, `rankOneNormalizingWeyl` has the group,
family, decomposition, closedness and subgroup binders of the published
`rankOneSelfAssociation`, without its Coxeter system and the finiteness
instance of the Weyl quotient. The universes `uI`, `uG` and `uV` are
independent. It assumes a maximal standard `J`, an irreducible actual
finite-length `σ` of `M J`, the published `IsCorollaryLeviCuspidal` condition
and reducibility of the actual normalized induction. It concludes

```text
∃ n : RelativeWeyl.normalizer T,
  (∀ x ∈ M J, n * x * n⁻¹ ∈ M J) ∧ n ∉ M J.
```

This is an obligation predicate. Its definition supplies no witness.

`rankOneAssociatedSubsetEquality_of_normalizingWeyl` assumes the actual Levi
Weyl identification and `Z_G(T) ≤ M J` for every `J`. Under these
assumptions it derives Worker 167's published `rankOneAssociatedSubsetEquality`
from `rankOneNormalizingWeyl`, using `associatedSubset_eq_of_normalizing_point`.

`rankOneNormalizingWeyl_of_selfAssociation` assumes the identification and
`rankOneSelfAssociation`. It takes any lift `n` of `longestRep actual J`
(`QuotientGroup.mk_surjective`), uses the target's every-lift normalization
conclusion, and applies `longestLift_not_mem`.

## Full rational scope

The remaining declarations belong to
`Langlands.Aubert.General.RationalPointFamily`.

`RationalRankOneNormalizingWeylStatement.{u,v}` has exactly the
quantifiers and visible premises of `RationalRankOneSelfAssociationStatement.{u,v}`,
in the same order. Its final predicate is `rankOneNormalizingWeyl` at
universes `.{u, u, max (u + 1) v}`, with `T := torusPoints i`. The scope is
every nonarchimedean local field, every connected reductive group scheme, the
actual maximal split torus, a generic cocharacter, the canonical
`pointTopology`, the literal `SimpleRoot i ν` labels and the actual
`parabolic`, `levi` and `unipotent` point subgroups. Representation carriers
are in `Type (max (u + 1) v)`. Positive characteristic and nonsplit or
non-quasisplit groups are included. The Coxeter binders `C` and `actual` and
the root-length, positive-simple-reflection, Levi-Weyl, minimality and
associated-subset premises do not occur in the conclusion. They are kept so
that the two statements have the same premises. When the simple-root type is
empty, `IsMaximalStandard` has no witness and both statements are vacuous.

`rationalRankOneSelfAssociation_of_normalizingWeyl` proves the full target
from the normalizer statement. It applies the published
`rationalRankOneSelfAssociation_of_associatedSubsetEquality`. It then uses
`rankOneAssociatedSubsetEquality_of_normalizingWeyl` with the target's
`actualLeviWeylIdentification` premise and with `pointCentralizer_le_levi`,
which derives `Z_G(T₀(F)) ≤ L_J` from the premise
`HasPointCentralizerComparison i`.

`rationalRankOneNormalizingWeyl_of_selfAssociation` proves the converse
through `rankOneNormalizingWeyl_of_selfAssociation`.
`rationalRankOneSelfAssociation_iff_normalizingWeyl` pairs the two
implications. It is an equivalence between two propositions that are both
still unproved. It proves neither of them.

## Dependencies and provenance

The provenance is internal. The new predicates restate an existing Library
target. The proofs are finite Coxeter combinatorics, subgroup quotient
arithmetic and logical assembly. No assertion from the original literature is
added. For orientation only: the published
`RepresentedParabolic.MaximalLeviSupercuspidalReducibilityStatement`
(Renard VII.1.3) concludes that some `g ∈ G(F)` outside the Levi normalizes
it. Moving that conclusion to the standard family and to a point of
`N_G(T₀(F))` is not done here.

| Published declaration | Use in this unit |
| --- | --- |
| `RationalRankOneSelfAssociationStatement`, `rankOneSelfAssociation` | Target and generic target, preserved unchanged. |
| `rankOneAssociatedSubsetEquality`, `rationalRankOneSelfAssociation_of_associatedSubsetEquality` (Worker 167) | Equality-only predicate and its reduction to the target. |
| `IsMaximalStandard`, `IsCorollaryLeviCuspidal` | The rank-one and restricted-cuspidality hypotheses, reused unchanged. |
| `exists_minimal_in_doubleCoset`, `isMinimal_inv`, `longestRep_mem`, `length_le_longestRep`, `mem_minimalReps`, `standardSubgroup_empty`, `simple_mem_standardSubgroup` | Intrinsic Coxeter constructions in `RelativeWeylIndexing`. |
| `minimalityLengthCriterion_proof`, `longestSurvivor_proof`, `exists_conj_simple_eq_of_isMinimal`, `mem_of_simple_mem_standardSubgroup`, `mem_positiveSimpleSet` | Published intrinsic Coxeter proofs. |
| `RelativeWeyl.inclusion`, `RelativeWeyl.normalizer`, `RelativeWeyl.centralizer` | The actual normalizer/full-centralizer quotients. |
| `pointCentralizer_le_levi` | Full point centralizer inside every actual standard Levi, from `HasPointCentralizerComparison`. |
| `isSemidirectDecomposition_of_standardCocharacterStatement`, `isSemidirectDecomposition_in_levi`, `simpleRelativeRootFintype` | The same decomposition and enumeration witnesses as in the target. |

The proofs use no Langlands classification, character independence,
geometric lemma, adjointness or cuspidal-support theorem. The representation
functors occur only in the inherited hypotheses, and no theorem about
irreducibility or composition factors is applied. Aubert Proposition 3.2 is
not used. To complete the original task one must still prove
`RationalRankOneNormalizingWeylStatement` (or the equality form) from the
reducibility hypothesis.
