# Proof of longest-representative Jacquet compatibility on rational points

Module: `Langlands.Representation.Aubert.General.RationalJacquetCompatibilityProof`,
namespace `Langlands.Aubert.General.RationalPointFamily`. Author: Worker 3977.

`rationalJacquetCompatibility : RationalJacquetCompatibilityStatement.{u, v}`
proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.RationalJacquetCompatibilityStatement`
of `Langlands.Representation.Aubert.General.RationalJacquetTarget`. It proves the
whole unapplied proposition, with independent universe parameters `u` and `v`
and no theorem parameters of its own. The statement's Lean/Markdown pair and the
pairs it imports are unchanged.

The proposition is the second equation of Aubert 1995, Theorem 1.7(2)
(printed p. 2181), with the conventions for `w_J`, `J'` and conjugation of
printed p. 2180. It covers every nonarchimedean local field and every connected
reductive group over it, with the actual maximal split torus and generic
cocharacter. Fix a standard subset `J` and an actual normalizer lift `n` of
`longestRep cs J`, and put `J' = associatedSubset cs J`. Then
`r_J ∘ D_G = transport_n ∘ D_{M_J'} ∘ r_J'` on the exact finite-length
Grothendieck groups. Here `D_G` is `rationalAlternatingOperator`, `D_{M_J'}` is
`rationalLeviAlternatingOperator` on the literal closed subgroup `levi i ν J'`,
`r_J` and `r_J'` are the normalized `jacquetK0` maps, and `transport_n` is
`conjugationK0` by `n`. All premises displayed by the target keep their scopes.

## Proof as implemented

The proof is a single application of two published theorems:

```
rationalJacquetCompatibility_of_rationalGeometricK0Expansion.{u, v}
  rationalGeometricK0Expansion.{u, v}
```

- `rationalGeometricK0Expansion : RationalGeometricK0ExpansionStatement.{u, v}`
  (module `RationalGeometricK0Expansion`, Worker 4021) is the published,
  premise-free geometric lemma on exact K0. For all standard subsets `I`, `J`
  and every section of the actual normalizer quotient, it writes
  `r_I ∘ i_J` as the sum of the actual normalized intersection terms
  `geometricTermK0` over `minimalReps cs I J`.
- `rationalJacquetCompatibility_of_rationalGeometricK0Expansion`
  (module `RationalJacquetGeometricAssembly`, Worker 165) proves
  `RationalGeometricK0ExpansionStatement.{u, v} → RationalJacquetCompatibilityStatement.{u, v}`.
  That expansion is its only premise.

The universe arguments are passed explicitly, so the expansion is used at
exactly the universes of the conclusion.

## The argument behind the composed declarations

1. **Rows of the geometric lemma**
   (`rationalIntersectionExpansions_of_rationalGeometricK0Expansion`). For the
   supplied point Coxeter system, `actualLeviWeylIdentification_of_rootLength`
   derives the standard-Levi Weyl identification from the target's root-length
   comparison. `rationalPointGeometricExpansion_of_rationalGeometricK0Expansion`
   specializes the expansion to the target's data. Then
   `rationalIntersectionExpansion_of_pointGeometricExpansion` identifies each
   geometric term with the literal restricted-intersection term
   `rationalIntersectionJacquetTerm`. The ambient and inside-Levi
   `ParabolicFiniteLength` packages come from `standardParabolicFiniteLength`
   and `standardLeviParabolicFiniteLength`, using the displayed topological,
   compact-limit and finite-length-preservation premises.
2. **Cancellation** (`rationalJacquetCompatibility_of_intersectionExpansions`,
   module `RationalJacquetCancellation`). Each row is composed with ambient
   `r_J`. `rationalIntersectionJacquetTerm_comp_ambient_eq_common` identifies
   the composite with `rationalCommonJacquetTerm`, using normalized Jacquet
   restriction in stages. Distributing the alternating sum gives
   `jacquetWeightedExpansion`, and its weighted cancellation leaves only the
   longest representative. `signed_sum_associatedFinsetEquiv` reindexes the
   remaining sum by the subsets of `associatedSubset cs J`, keeping the
   unadjusted signs `(-1)^|I|`. `rationalJacquetLongestTermReduction`
   identifies each summand with the associated-Levi term transported by `n`.
   `sum_transportedLeviJacquetTerm` assembles the claimed composite. A private
   choice lemma gives a normalizer section that takes the value `n` at
   `longestRep cs J`, so every lift `n` is covered.

## Dependencies

Proof-body dependencies of this theorem:

- `rationalJacquetCompatibility_of_rationalGeometricK0Expansion`, whose body
  uses `rationalIntersectionExpansions_of_rationalGeometricK0Expansion` and
  `rationalJacquetCompatibility_of_intersectionExpansions`;
- `rationalGeometricK0Expansion`, whose body uses
  `rationalGeometricK0Expansion_of_standardParabolicPoints` and
  `GroupScheme.standardParabolicPointsStatement_proof`.

Transitive uses, by scope. These were checked by computing, in a private
diagnostic, every constant reachable from the theorem through the types and
values of the constants it uses. Module names below are relative to
`Langlands.Representation`.

- **Geometric lemma.** Used, at the target's full scope, through
  `rationalGeometricK0Expansion`. Its proof builds the support filtration from
  the published closed-subgroup Mackey filtration
  (`Geometric.ClosedSubgroupMackeyProof`, `Geometric.SmoothSupportFiltration`,
  `Aubert.General.ParabolicSupportFiltration`). It orders the orbits with
  `GroupScheme.standardParabolicPointsStatement_proof`, compares the graded
  pieces with the normalized geometric terms, and cancels the Haar correction
  characters with `geometricEpsilon_mul_eq_one`. It assumes no expansion
  premise.
- **Transitivity.** Normalized Jacquet restriction in stages
  (`RationalJacquetStages`, `RationalJacquetStagesK0`,
  `Aubert.General.JacquetStages`) and induction in stages
  (`Induction.SplitStagesComparison`, `Induction.CompactTransitivityProof`) are
  used through published proofs.
- **Adjointness.** Not used. No constant of `Parabolic.NaturalFirstAdjointness`
  or any other Frobenius-reciprocity module is reachable.
- **Cuspidal support.** No cuspidal-support theorem is used. Two
  generic helpers that live in `CuspidalSupport` modules are reachable:
  `Jacquet.coinvariantsMapEquiv` (coinvariants transported along a group
  homomorphism, `CuspidalSupport.GroupTransport`) and
  `CuspidalSupport.JacquetLength.compSubrepresentationOrderIso` (subrepresentations
  are unchanged by composition with a surjection,
  `CuspidalSupport.InducedJacquetCount`).
- **Langlands classification.** Not used. The only reachable constants of
  `Classification.FiniteLengthProof` are the generic lemmas
  `FiniteLengthAssembly.length_comp_surjective` and
  `FiniteLengthAssembly.finiteLength_comp_surjective_iff` (length is unchanged by
  composition with a surjective homomorphism).
- **Character independence.** Not used. The epsilon cancellation detects
  rational characters of tori algebraically, not by linear independence of
  representation characters.

The imported module closure is much larger than the reachable constants; for
example it contains Harish-Chandra and cuspidal-support results that the proof
does not use. Aubert Proposition 3.2 and the original application to
Theorem 3.6 are not used as evidence. The theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Scope

The scope is the target's: every connected reductive group scheme over every
nonarchimedean local field, including positive characteristic and nonsplit or
non-quasisplit groups. The topology is `pointTopology`, the labels are the
literal `SimpleRoot i ν`, the Weyl quotient is the torus normalizer modulo its
full centralizer, and representation carriers lie in `max (u + 1) v`. Empty
simple-root sets and empty or full `J` are allowed. No premise is added beyond
the target's own. `StandardCocharacterStatement`,
`StandardLeviIntersectionStatement`, `StandardLeviConjugationStatement`, the
normalizer and centralizer comparisons, `RootLengthComparison`,
`PositiveSimpleReflectionComparison`, `minimalityLengthCriterion` and
`associatedSubsetLaws` all remain premises of the target.
