# Reduction of rational rank-one self-association

Author: Worker 167.

This internal supporting unit isolates the subset equality in the published
`RationalRankOneSelfAssociationStatement` and proves that it suffices for
the full target under that target's existing premises. In particular, those
premises already supply the actual subgroup conjugation needed to deduce
normalization by every lift of the specified longest representative.
The implication from reducibility to the subset equality remains unproved.
This unit therefore does not prove the full self-association statement.

## Generic equality and normalization

The declarations in this section belong to `Langlands.Aubert.General`.

`rankOneAssociatedSubsetEquality` retains the maximal-standard-Levi,
irreducibility, restricted Levi cuspidality and reducibility hypotheses of
`rankOneSelfAssociation`, but concludes only
`RelativeWeylIndexing.associatedSubset actual J = J`. It uses the same actual
normalized induction functor and finite-length representation objects.
The generic group, indexing and carrier universes remain independent.
This is an obligation predicate; its definition provides no witness.

`longestLift_normalizes_of_associatedSubset_eq` assumes actual
associated-Levi conjugation and the subset equality for `J`. For any
`n : RelativeWeyl.normalizer T` with quotient class
`RelativeWeylIndexing.longestRep actual J`, actual conjugation gives

```text
(M (associatedSubset actual J)).map (MulAut.conj n) = M J.
```

Rewriting the subset equality gives a conjugate-image equality for `M J`
itself. The published `conjugationMembership_of_map_eq` first yields the
inverse-conjugation membership equivalence. The proof applies it at
`n * x * n⁻¹`, simplifies the group products and reverses the equivalence.
The result is exactly

```text
x ∈ M J ↔ n * x * n⁻¹ ∈ M J.
```

This lemma needs only group structure and the displayed indexing and
conjugation data. Topology, local compactness, nonarchimedean structure and
decidable equality on the labels are omitted from its parameters.
It quantifies every lift with the specified class; it does not choose a
lift or assert that conjugation is elementwise trivial.

`rankOneSelfAssociation_iff_associatedSubsetEquality` assumes actual
associated-Levi conjugation. The forward implication projects the subset
equality from the full target. The reverse implication pairs the equality
with `longestLift_normalizes_of_associatedSubset_eq`. This conditional
generic equivalence is not a theorem of self-association for arbitrary
subgroup families.

## Full rational scope

The remaining declarations belong to
`Langlands.Aubert.General.RationalPointFamily`.

`RationalRankOneAssociatedSubsetEqualityStatement.{u,v}` has precisely
the quantifiers and visible premises of the published
`RationalRankOneSelfAssociationStatement.{u,v}`. Its final predicate is
`rankOneAssociatedSubsetEquality` in place of `rankOneSelfAssociation`.
It keeps every nonarchimedean local field, every connected reductive
group scheme, the actual maximal split torus and generic cocharacter,
the canonical evaluation topology `pointTopology`, literal
`SimpleRoot i ν` labels and the actual `parabolic`, `levi` and `unipotent`
point subgroups. Both universe parameters are independent. The generic
predicate is specialized at `.{u,u,max (u + 1) v}`, so representation
carriers have universe `max (u + 1) v`, just as in the target.

The standard-cocharacter and standard-Levi-intersection statements,
actual root-system realization, closedness conditions, point-normalizer
and point-centralizer comparisons, root-length and positive-simple-
reflection comparisons, actual Levi Weyl identification, minimality
criterion and associated-subset laws are retained in the original order.
In particular the actual Levi Weyl identification remains a premise even
though the normalization deduction does not use it. The restricted
Levi cuspidality predicate is unchanged. There is no nonempty-root
assumption: when the simple-root type is empty, `IsMaximalStandard`
has no witness.

`rationalRankOneAssociatedSubsetEquality_of_selfAssociation` projects
the first conclusion pointwise, retaining all the displayed parameters.

`rationalRankOneSelfAssociation_of_associatedSubsetEquality` first uses
`GroupScheme.standardLeviConjugationStatement_of_standardCocharacterStatement`
on the existing `hStandard` premise. This produces the published
all-test-scheme `StandardLeviConjugationStatement` without adding a new
premise to the target. Then `associatedLeviConjugation_of_standard`
uses the target's actual-root and quotient comparisons to supply
`actualAssociatedLeviConjugation` for the actual rational-point family.
The generic equivalence proves the full target from the equality-only
predicate.

`rationalRankOneSelfAssociation_iff_associatedSubsetEquality` pairs these
two implications. It proves an equivalence between two still-unproved
propositions, not either proposition alone. There is no additional theorem
parameter on this equivalence and no finite-length-preservation premise.
Positive characteristic, nonsplit and non-quasisplit groups retain the
scope of the original target.

## Declaration-level dependencies and provenance

This is an internal reduction of existing Library statements. The new
predicate is obtained by projecting the conclusion of an existing target;
the proof is subgroup transport and logical assembly. No independent
assertion from the original literature is introduced.

| Published declaration or predicate | Use in this unit |
| --- | --- |
| `Langlands.Aubert.General.rankOneSelfAssociation` in `GeneralCorollaryTargets` | Original generic target, including the every-lift conclusion. |
| `Langlands.Aubert.General.IsMaximalStandard` and `IsCorollaryLeviCuspidal` in `GeneralCorollaryTargets` | Original rank-one and actual restricted-Jacquet hypotheses, reused without modification. |
| `Langlands.Aubert.General.RationalPointFamily.RationalRankOneSelfAssociationStatement` in `General.RationalCorollaryTargets` | Original complete rational target, preserved without editing its pair or imported pairs. |
| `Langlands.Group.RelativeWeylIndexing.actualAssociatedLeviConjugation` | Actual image equality for every lift of the specified longest quotient class. This is an explicit hypothesis of the generic equivalence and a derived conclusion in the rational proof. |
| `Langlands.Aubert.General.conjugationMembership_of_map_eq` in `General.JacquetTarget` | Converts an actual conjugate subgroup image equality to inverse-conjugation membership. |
| `Langlands.GroupScheme.standardLeviConjugationStatement_of_standardCocharacterStatement` in `Rational.StandardLeviConjugationAssembly` | Derives the structural conjugation statement from the target's existing `hStandard`, taking its standard-cocharacter-existence conjunct for every face. |
| `Langlands.Aubert.General.RationalPointFamily.associatedLeviConjugation_of_standard` in `General.RationalAssociatedLeviConjugation` | Derives actual associated-Levi image equality from that structural statement and the target's existing actual-root, length, reflection, minimality and subset premises. |
| `isSemidirectDecomposition_of_standardCocharacterStatement` and `isSemidirectDecomposition_in_levi` | The same ambient and restricted decomposition witnesses used by the original target. |

The structural assembly theorem invokes
`standardLevi_eq_comap_of_standardCocharacter_exists`, which uses
`finite_simpleRelativeRoots_of_standardCocharacter_exists` and
`standardLevi_eq_comap_of_rootSubset_image`, together with
`standardLevi_comap_innerIso_inv_eq_of_relativeWeyl_eq` for lift
independence. These are existing structural deductions; the
unconditional standard-cocharacter statement is not proved here.

The actual rational adapter invokes `rootSet_associatedSubset` to identify
the associated subset with the inverse-longest image of the actual simple
roots. It cancels the Weyl action and uses
`levi_map_conj_of_character_image`, ultimately evaluating the structural
all-test subgroup-functor equality on rational points. The quotient remains
the actual normalizer modulo the full centralizer, and no arbitrary
relabeling is used.

The new proofs use no Langlands classification, character independence,
geometric lemma, adjointness or cuspidal-support theorem. Representation
functors occur in the predicates inherited from the target; no theorem
about their irreducibility or composition factors is applied. In
particular, the representation-theoretic implication from reducibility
to `associatedSubset actual J = J` is still required for completion of the
original proof task. This unit makes no use of Aubert Proposition 3.2.
