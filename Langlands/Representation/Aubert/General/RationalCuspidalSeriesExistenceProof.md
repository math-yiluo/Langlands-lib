# Cuspidal-series existence on actual rational points

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.RationalCuspidalSeriesExistenceStatement`
from `RationalSupportCategoryTargets`, with no extra hypothesis. The proof is
the theorem

```
theorem rationalCuspidalSeriesExistence :
    RationalCuspidalSeriesExistenceStatement.{u, v}
```

It proves the whole unapplied proposition at independent universes `u` and `v`
and takes no further parameters. The source is Renard, Corollaire VI.2.1
(printed p. 139, PDF p. 145), read with Aubert's Notation 1.6 (printed p. 2181).

## What is proved

Fix a nonarchimedean local field `k` and a connected reductive group scheme `G`
over `Spec k`. Fix a maximal split torus `i : T ⟶ G` and a generic cocharacter
`ν`. Give `RationalPoint k G.X` the canonical evaluation topology
`pointTopology`, with the target's `LocallyCompactSpace`, `NonarchimedeanGroup`
and `T2Space` instances. Assume the target's premises `hStandard`, `hInter`,
`hRoots`, `hU` and `hM`. Let `π` be an irreducible smooth complex
representation of `RationalPoint k G.X`, with carrier in universe
`max (u + 1) v`. Then there is a set `I` of actual simple roots
(`SimpleRoot i ν`) with `IsInCuspidalSeries` at `I`. That is, there is an
irreducible smooth representation `σ` of the actual standard Levi
`levi i ν I`. It is `IsLeviCuspidal`: its actual normalized Jacquet module
vanishes along every proper standard parabolic of `levi i ν I`. And `π` is a
`SmoothRep.IsSubquotient` of the actual normalized induction
`(normalizedInductionFunctor (h I) (hU I)).obj σ`.

The families, decompositions, closedness proofs and universes are exactly those
of the target. The proof uses no restriction on `k`, `G` or the root data. It
covers positive characteristic, nonsplit and non-quasisplit groups, empty
simple-root sets and relative rank zero. In relative rank zero the full index
set is empty. Step 2 below then picks `I = ∅`, and step 3 is vacuous because
`∅` has no proper subset.

## Declarations

- `rationalCuspidalSeriesExistence_of_compactSpace` fixes `k`, `G`, `T`, `i`
  and `hi`. It takes the target's remaining binders, plus one more premise:
  `∀ I, CompactSpace (Induction.LeftQuotient (parabolic i ν I))`. Its
  conclusion is the target's `CuspidalSeriesExistenceTarget`, with the same
  families and decompositions `h` and `hL`, at universes `u, u, max (u + 1) v`.
- `rationalCuspidalSeriesExistence_of_dynamicParabolicQuotientCompact` proves
  `BruhatTits.DynamicParabolicQuotientCompactStatement.{u} →
  RationalCuspidalSeriesExistenceStatement.{u, v}`. For each `I` it gets the
  extra premise from the published adapter
  `Langlands.Aubert.General.compactSpace_leftQuotient_parabolic`. Via
  `hStandard`, that adapter writes `parabolic i ν I` as an actual dynamic
  parabolic. It then takes the `Pg` component of the compactness statement.
- `rationalCuspidalSeriesExistence` applies that implication to the published
  unconditional theorem `Langlands.BruhatTits.dynamicParabolicQuotientCompact`.

So the extra compactness premise is discharged from the displayed data. It is
not a new hypothesis of the final theorem.

## The implemented proof

The argument takes the minimal-nonzero-Jacquet route of the published
`rationalCuspidalEmbedding` proof and replays it here. That theorem cannot be
applied directly. Its statement has three premises the target lacks: an
endpoint premise (`StandardParabolicEndpointsStatement`), compactness and a
compact-limit property. The endpoint premise is not needed: the replayed proof
never uses it. The other two are discharged as follows.

- The compact-limit property holds for every standard unipotent radical
  `unipotent i ν I`. It follows from `hStandard` by
  `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`.
- Compactness of `P_I \ G` is the extra premise above. It is discharged in the
  final theorem by `dynamicParabolicQuotientCompact`.

Here `r_I` is the actual normalized Jacquet functor
`jacquetFunctor (h I) (hU I)`. For an irreducible `π`:

1. `r_S π ≠ 0`, where `S = Finset.univ` is the full index set. By
   `unipotent_univ_eq_bot`, `unipotent i ν Finset.univ` is trivial. So the
   relation span is zero, and a nonzero vector of `π` stays nonzero in the
   Jacquet module (`Jacquet.Localization.mk_eq_zero`).
2. Choose an index `I` of minimal cardinality with `r_I π` nontrivial. This
   uses well-foundedness of `measure Finset.card`. Every proper `K ⊂ I` gives
   `leviIndex I K` of smaller cardinality (`card_leviIndex`). Hence
   `r_{leviIndex I K} π` is a subsingleton.
3. `r_I π` is `IsLeviCuspidal`. Take a proper `K`. Every vector of `r_I π`
   lies in the relation span of `U_{leviIndex I K} ∩ L_I`. This step uses
   `CuspidalEmbedding.mem_relations_of_subsingleton` and three facts:
   - the product decomposition `unipotent_product_of_subset`;
   - the containment `unipotent_le_parabolic_of_subset`, combined with
     `(h I).le_normalizer`;
   - the modulus identity
     `CuspidalEmbedding.closedNormalizerCharacter_eq_one_of_compactLimit`,
     used with the compact-limit property above and
     `Jacquet.inverseHalfCharacter_eq_one`.

   Then `CuspidalEmbedding.subsingleton_jacquet_of_forall_mem_relations` gives
   the vanishing.
4. `π` is irreducible, so it is a simple module and finitely generated over
   `MonoidAlgebra ℂ (RationalPoint k G.X)` (instance search). `P_I \ G` is
   compact, so `JacquetFiniteGeneration.finite_of_compactQuotient` (Renard
   VI.1.3) makes `r_I π` finitely generated over `levi i ν I`. Its
   subrepresentation lattice is therefore coatomic. As `r_I π` is nonzero, it
   has a maximal proper subrepresentation `T₀`. The quotient
   `σ = SmoothRep.quotient (r_I π) T₀` is irreducible by
   `SmoothRep.RenardIrreducibleExistence.quotient_isIrreducible_of_isCoatom`.
5. `σ` is `IsLeviCuspidal`. The actual Jacquet functors of `L_I` preserve
   surjections (`CuspidalEmbedding.jacquet_map_surjective`). So they vanish on
   the quotient `σ` of `r_I π`.
6. First adjointness turns the quotient map `q : r_I π → σ` into an
   intertwiner `F : π → i_I σ`, where `i_I` is actual normalized induction.
   The equivalence used is
   `RationalPointFamily.FirstAdjointness.equiv i ν hStandard hG hi hν I (hU I)`.
   `F` is nonzero because `q` is nonzero and the equivalence is injective.
   `Representation.IsIrreducible.injective_or_eq_zero` makes `F` injective.
7. An injection is a subquotient (`SmoothRep.IsSubrepresentation.isSubquotient`).
   This gives `IsInCuspidalSeries` at `I` with the irreducible cuspidal `σ`.

The proof thus gives an embedding `π ↪ i_I σ`, which is stronger than the
subquotient conclusion the target asks for.

## Dependencies and scope

The declarations the proof uses directly, with their modules:

- `RationalCuspidalEmbeddingProof`: the four public helper lemmas
  `CuspidalEmbedding.mem_relations_of_subsingleton`,
  `CuspidalEmbedding.subsingleton_jacquet_of_forall_mem_relations`,
  `CuspidalEmbedding.closedNormalizerCharacter_eq_one_of_compactLimit` and
  `CuspidalEmbedding.jacquet_map_surjective`. The theorem
  `rationalCuspidalEmbedding` itself, with its endpoint premise, is not used.
- `RationalUnipotentRegularity`:
  `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`.
  It goes through the published `BruhatTits.dynamicUnipotentCompactOpenContainment`.
- `RationalInductionDualityReduction`: `compactSpace_leftQuotient_parabolic`.
- `BruhatTits.Parabolic.QuotientCompactProof`: `dynamicParabolicQuotientCompact`,
  an unconditional proof of Renard's compactness of `G/P` (V.5.1 corollary).
  It goes through the algebraic flag quotient and compactness of points of
  proper schemes.
- `JacquetFiniteGeneration`: `JacquetFiniteGeneration.finite_of_compactQuotient`
  (Renard VI.1.3). It assumes `CompactSpace (Induction.LeftQuotient P)`, which
  step 4 supplies.
- `RationalFirstAdjointness`: `RationalPointFamily.FirstAdjointness.equiv`.
  This is actual normalized first adjointness for the actual standard
  parabolic `I`. It specializes `General.FirstAdjointness.equiv`, with
  unimodularity of the radical discharged from `hStandard` by
  `standardUnipotent_isUnimodular_of_standardCocharacterStatement`. Its
  construction uses the Jacquet character reciprocity
  `Jacquet.CharacterReciprocity.evaluation` from `Jacquet.ReciprocityProof`.
- `RationalEndpoint`: only the structural lemma `unipotent_univ_eq_bot`. The
  endpoint statement itself is not used.
- `RationalInductionStagesGeometry`: `unipotent_product_of_subset` and
  `unipotent_le_parabolic_of_subset`.
- `Smooth.RenardIrreducibleExistenceProof`:
  `quotient_isIrreducible_of_isCoatom`. `Classification.SupercuspidalSupport`:
  only the elementary subquotient lemmas
  `SmoothRep.IsSubrepresentation.isSubquotient`,
  `SmoothRep.isSubquotient_iff_exists` and `SmoothRep.hom_hom_surjective`.

The transitive dependencies were audited in Lean. The audit walked the type and
value of every constant reachable from `rationalCuspidalSeriesExistence`:
about 125,000 constants, including constants from 1,948 `Langlands` modules.
The only adjointness results reached are the `FirstAdjointness` declarations
above. Some algebraic-group constants matched the search words: `adjoint`,
Frobenius, power-exponent and `SplitComponent.imageClassify` names. Apart from
these, no constant reached matches classification, Langlands quotient,
geometric lemma, character independence, tempered, Casselman or
Jacquet-exponent names. The
only declarations reached from `Classification.SupercuspidalSupport` are the
subquotient lemmas listed above. `#print axioms rationalCuspidalSeriesExistence`
reports only `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Steps 1–7 come from this task's carried-over shared draft (revision 1,
`RationalCuspidalSeriesExistenceReduction`). There they formed a conditional
reduction to `DynamicParabolicQuotientCompactStatement`. This module renames
it and adds the final application to the published
`dynamicParabolicQuotientCompact`, which makes the result unconditional.
