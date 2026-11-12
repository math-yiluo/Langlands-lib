# Involutivity of the support-adjusted graded Aubert operator

Author: Worker 104.

`Langlands.Aubert.adjustedInvolutivity.{uF, uV} F T` proves exactly the
published `Langlands.Aubert.AdjustedInvolutivityStatement.{uF, uV} F T`.
It has only the target's ambient parameters: a prime `p` with
`[Fact p.Prime]`, `F : PadicField.{uF} p`, and `T : F.TopologicalData`.
The field and representation universes are independent. The operator acts on
the direct sum of the actual exact finite-length GL Grothendieck groups in
all natural ranks, including zero. No multiplicativity, binary exactness,
induction ring law, polynomial comparison, or additional theorem premise
is assumed. The target pair and every pair it imports are unchanged.

## Implemented proof

Write `D` for the unadjusted operator and `A` for its support adjustment.
For an actual irreducible `π`, `Langlands.Aubert.irreducibleImage` gives an
actual irreducible `πD` and an integer `s = 1` or `s = -1` with
`D[π] = s • [πD]`. Hence `s * s = 1`. The published
`Langlands.Aubert.involutivity` implies `D[πD] = s • [π]`.

The composition-factor map sends `[π]` and `[πD]` to their actual
irreducible generators. Each generator is coefficientwise effective, so both
`s • D[π]` and `s • D[πD]` are effective in these coordinates.
`Langlands.Aubert.supportSign_eq_of_effective` therefore identifies both
support signs with `s`. Applying
`Langlands.Aubert.adjustedOperator_irreducible` now gives
`A[π] = [πD]` and `A[πD] = [π]`. The private irreducible helper implements
this calculation uniformly in every rank. The imported irreducible-image
result itself handles rank zero with the actual identity operator.

`Langlands.Aubert.adjustedOperator_involutive` extends this calculation to
every class in each rank. It compares `A.comp A` with the identity after
composition with actual Jordan–Hölder realization, using
`Langlands.SmoothRep.eq_realizeIrreducibles_of_irreducible`. Composing with
`Langlands.SmoothRep.IrreducibleGrothendieckProof.factorMap` and applying
`Langlands.SmoothRep.IrreducibleGrothendieckProof.realize_comp_factorMap`
then proves equality on the entire exact quotient. This retains the relations
from all actual finite-length short exact sequences, including nonsplit ones.
The coordinate calculations use
`Langlands.SmoothRep.IrreducibleGrothendieckProof.factorMap_ofRepresentation`,
`Langlands.SmoothRep.IrreducibleGrothendieckProof.compositionFactors_irreducible`, and
`Langlands.SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass`.

Finally `Langlands.Aubert.adjustedInvolutivity` applies
`DirectSum.linearMap_ext` to the square of the graded linear map.
`Langlands.Aubert.gradedAdjustedOperator_homogeneous` reduces its value on
each homogeneous inclusion to `adjustedOperator_involutive` in that rank.
The direct-sum universal property gives the desired identity on every graded
class. This is an additive proof and does not require a segment basis.

## Source and provenance

The source assertion is the involutivity in Aubert, *Dualité dans le groupe
de Grothendieck de la catégorie des représentations lisses de longueur finie
d'un groupe réductif p-adique* (1995), Definition 2.1 and Theorem 2.3,
printed pp.2184–2185. The unadjusted input is Theorem 1.7(3), printed
pp.2181–2183. Those original passages were read directly. Registered source:
`aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
The new proof is internal assembly of published Lean results, using the
unique effective-sign characterization already proved in `SupportSign`.
It does not reproduce the segment-polynomial proof of the whole comparison
in Theorem 2.3. It retains the existing complex coefficients, upper block
parabolics, positive induction and inverse Jacquet half-moduli, right
translation, and saturated representation carriers `Type (max uF uV)`.

## Transitive representation and classification dependencies

The direct representation-theoretic inputs are `irreducibleImage`,
`involutivity`, `supportSign_eq_of_effective`, and the defining adjusted
irreducible formula, all in `Langlands.Aubert`. Their types and proof bodies
retain the published support, corrected signed-effectivity, geometric-lemma,
normalized induction/Jacquet and finite-length chains. In particular,
`irreducibleImage` applies
`Langlands.Aubert.irreducibleImage_of_signedEffectivity` to
`Langlands.Aubert.signedEffectivity`. The reduction uses
`Langlands.CuspidalSupport.normalizedQuasicuspidalEmbedding` and
`Langlands.Aubert.alternatingOperator_normalizedInductionK0_quasicuspidal`.
The sign construction also uses that actual quasicuspidal embedding and
`signedEffectivity`. These imports are reused without modification; the
original defective Aubert Proposition 3.2 and uncorrected Theorem 3.6 argument
are not additional inputs.

The normalized-induction finite-length chain reaches these exact declarations:

- `Langlands.Classification.normalizedInductionFiniteLength`;
- `Langlands.Classification.ProductLengthProof.irreducibleLevi` and
  `Langlands.Classification.ProductLengthProof.leviPreservation`;
- `Langlands.CuspidalSupport.padicLeviAdmissibleFactorization`;
- `Langlands.Classification.irreducibleProductFiniteLength`;
- `Langlands.Classification.irreducibleProductEmbedding`,
  `Langlands.Classification.irreducibleProduct_embedding`,
  `Langlands.Classification.irreducible_supercuspidalProduct_embedding`, and
  `Langlands.Classification.normalizedProduct_embedding_of_factor_embeddings`;
- `Langlands.CuspidalSupport.cuspidalEmbedding` and
  `Langlands.CuspidalSupport.padicLeviCuspidalFactorization`;
- `Langlands.CuspidalSupport.glCuspidalTensor`,
  `Langlands.CuspidalSupport.cuspidalInductionLength`, and
  `Langlands.Parabolic.orderedProductRegrouping`.

Thus the theorem's lack of a classification premise does not assert transitive
independence. Classification is permitted by this task. The following complete
Classification-module inventory records exact declaration names, including
auxiliary definitions and generated proof helpers rather than treating every
constant in those modules as a classification theorem. It was obtained by
recursively traversing the final theorem's type and proof, then each reached
project declaration's type and value, including opaque values and inductive
constructors. The traversal reached 8,530 project constants in 692 modules,
with 137 constants originating in `Langlands.Representation.Classification`.
The imported versions are those in Library commit
`04a311a4c16d58815bdcde73a66a203a2edb06dc`; the new proof is the pair containing
this Markdown. This is a declaration-use inventory, not a semantic independence
certificate. Unused modules in the import closure are not counted.

The complete outer telescope was also checked by assigning the unapplied
`@Langlands.Aubert.adjustedInvolutivity.{uF, uV}` to the target's full dependent
function type. Lean reports only `propext`, `Classical.choice`, and `Quot.sound`
as axioms of the final theorem.

### `Langlands.Representation.Classification.FiniteLengthProof`

```text
Langlands.FiniteLengthAssembly.complementaryProjection
Langlands.FiniteLengthAssembly.complementaryProjection._proof_1
Langlands.FiniteLengthAssembly.complementaryProjection._proof_2
Langlands.FiniteLengthAssembly.complementaryProjection_surjective
Langlands.FiniteLengthAssembly.finiteLength_comp_surjective_iff
Langlands.FiniteLengthAssembly.finiteLength_normalizedJacquet_of_refinements
Langlands.FiniteLengthAssembly.finiteLength_of_complement
Langlands.FiniteLengthAssembly.finiteLength_of_complement._simp_1_2
Langlands.FiniteLengthAssembly.finiteLength_of_complement._simp_1_3
Langlands.FiniteLengthAssembly.finiteLength_of_injective
Langlands.FiniteLengthAssembly.finiteLength_of_refinedJacquet
Langlands.FiniteLengthAssembly.finiteLength_of_surjective
Langlands.FiniteLengthAssembly.finite_of_surjective
Langlands.FiniteLengthAssembly.finite_summand
Langlands.FiniteLengthAssembly.isAdmissible_levi_subrepresentation
Langlands.FiniteLengthAssembly.isAdmissible_normalizedJacquet
Langlands.FiniteLengthAssembly.length_comp_surjective
Langlands.FiniteLengthAssembly.length_eq_add_of_complement
Langlands.FiniteLengthAssembly.normalizedJacquet_eq_twist
Langlands.FiniteLengthAssembly.refinedJacquetMap_surjective
Langlands.FiniteLengthAssembly.refinement_measure_lt
Langlands.FiniteLengthAssembly.refinement_measure_lt._proof_1_1
Langlands.Parabolic.normalizedJacquetFiniteLength
```

### `Langlands.Representation.Classification.IrreducibleProductEmbedding`

```text
Langlands.Classification.irreducibleProductEmbedding
Langlands.Classification.irreducibleProduct_embedding
Langlands.Classification.irreducible_supercuspidalProduct_embedding
Langlands.Classification.normalizedProduct_embedding_of_factor_embeddings
Langlands.FiniteTensor.externalMap_injective
```

### `Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement`

```text
Langlands.Classification.IrreducibleProductEmbeddingTheorem
```

### `Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof`

```text
Langlands.Classification.irreducibleProductFiniteLength
_private.Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof.0.Langlands.Classification.flattenSupercuspidalFactors
_private.Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof.0.Langlands.Classification.flattenSupercuspidalFactors_obj
```

### `Langlands.Representation.Classification.NormalizedProductFiniteLengthProof`

```text
Langlands.Classification.ProductLengthProof.finiteLength_of_injective
Langlands.Classification.ProductLengthProof.finiteLength_of_range_eq_ker
Langlands.Classification.ProductLengthProof.finiteLength_of_surjective
Langlands.Classification.ProductLengthProof.irreducibleLevi
Langlands.Classification.ProductLengthProof.leviPreservation
Langlands.Classification.ProductLengthProof.step
Langlands.Classification.normalizedInductionFiniteLength
```

### `Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement`

```text
Langlands.Classification.IrreducibleProductFiniteLength
```

### `Langlands.Representation.Classification.ProductLeviMinimalIndex`

```text
Langlands.ProductLeviMinimalIndex.blockIndex_eq_flatten
Langlands.ProductLeviMinimalIndex.blockIndex_flatten_index
Langlands.ProductLeviMinimalIndex.blockIndex_flatten_index_eq_iff
Langlands.ProductLeviMinimalIndex.blockIndex_flatten_index_ne
Langlands.ProductLeviMinimalIndex.blockIndex_flatten_index_ne._simp_1_1
Langlands.ProductLeviMinimalIndex.blockWeyl_flatten_le
```

### `Langlands.Representation.Classification.Supercuspidal`

```text
Langlands.GeneralLinear.BlockShape.conjugateUnipotent
Langlands.GeneralLinear.IsSupercuspidal
Langlands.GeneralLinear.SupercuspidalRep
Langlands.GeneralLinear.isSupercuspidal_of_equiv
Langlands.GeneralLinear.supercuspidalProperty
Langlands.Jacquet.coinvariantsEquiv
Langlands.Jacquet.coinvariantsEquiv._proof_1
Langlands.Jacquet.coinvariantsEquiv._proof_2
Langlands.Jacquet.coinvariantsEquiv._proof_3
Langlands.Jacquet.coinvariantsEquiv._proof_4
Langlands.Jacquet.coinvariants_subsingleton_iff
```

### `Langlands.Representation.Classification.SupercuspidalContragredientAux`

```text
Langlands.GeneralLinear.isSupercuspidal_iff_standard
Langlands.Jacquet.coinvariantsConjEquiv
Langlands.Jacquet.coinvariantsConjEquiv._proof_1
Langlands.Jacquet.coinvariantsConjEquiv._proof_2
Langlands.Jacquet.coinvariantsConjEquiv._proof_3
Langlands.Jacquet.coinvariantsConjEquiv._proof_4
Langlands.Jacquet.coinvariantsConjEquiv._proof_5
Langlands.Jacquet.coinvariantsConjEquiv._proof_6
Langlands.Jacquet.coinvariants_conj_subsingleton_iff
Langlands.eq_zero_of_smoothDual_annihilates
Langlands.isIrreducible_iff_of_equiv
Langlands.isIrreducible_of_smoothContragredient
Langlands.isIrreducible_smoothContragredient_iff_of_bidual
```

### `Langlands.Representation.Classification.SupercuspidalSupport`

```text
Langlands.SmoothRep.IsQuotient.isSubquotient
Langlands.SmoothRep.IsSubquotient.of_iso_right
Langlands.SmoothRep.IsSubrepresentation.isSubquotient
Langlands.SmoothRep.hom_hom_injective
Langlands.SmoothRep.hom_hom_surjective
Langlands.SmoothRep.isSubquotient_iff_exists
Langlands.SmoothRep.isSubquotient_iff_exists.match_1_1
```

### `Langlands.Representation.Classification.SupercuspidalTwist`

```text
Langlands.GeneralLinear.BlockShape.determinant_eq_one_of_mem_unipotentSubgroup
```

### `Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof`

```text
Langlands.Classification.TwoFactorCommutativity.annihilator
Langlands.Classification.TwoFactorCommutativity.annihilator._proof_1
Langlands.Classification.TwoFactorCommutativity.annihilator._proof_2
Langlands.Classification.TwoFactorCommutativity.annihilator._proof_3
Langlands.Classification.TwoFactorCommutativity.annihilator._proof_4
Langlands.Classification.TwoFactorCommutativity.annihilatorQuotientEquiv
Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict
Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_1
Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_10
Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_11
Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_2
Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_3
Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_4
Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_5
Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_6
Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_7
Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_8
Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict._proof_9
Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict_eq_zero_iff
Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict_surjective
Langlands.Classification.TwoFactorCommutativity.annihilator_antitone
Langlands.Classification.TwoFactorCommutativity.annihilator_bot
Langlands.Classification.TwoFactorCommutativity.annihilator_top
Langlands.Classification.TwoFactorCommutativity.canonicalTopology
Langlands.Classification.TwoFactorCommutativity.dualSeries
Langlands.Classification.TwoFactorCommutativity.dualSeries._proof_1
Langlands.Classification.TwoFactorCommutativity.dualSeries._proof_2
Langlands.Classification.TwoFactorCommutativity.dualSeries._proof_3
Langlands.Classification.TwoFactorCommutativity.dualSeries._proof_4
Langlands.Classification.TwoFactorCommutativity.dualSeries_graded
Langlands.Classification.TwoFactorCommutativity.gelfandKazhdan_inverseTranspose
Langlands.Classification.TwoFactorCommutativity.gelfandKazhdan_inverseTranspose._proof_1_1
Langlands.Classification.TwoFactorCommutativity.haveSameJordanHolderFactors_dual_comp
Langlands.Classification.TwoFactorCommutativity.haveSameJordanHolderFactors_of_comp
Langlands.Classification.TwoFactorCommutativity.isAdmissible_of_isIrreducible
Langlands.Classification.TwoFactorCommutativity.isSmooth_quotientRep
Langlands.Classification.TwoFactorCommutativity.isSmooth_toRepresentation
Langlands.Classification.TwoFactorCommutativity.productSmoothDual
Langlands.Classification.TwoFactorCommutativity.quotientProjection
Langlands.Classification.TwoFactorCommutativity.quotientProjection._proof_1
Langlands.Classification.TwoFactorCommutativity.quotientRepEquiv
Langlands.Classification.TwoFactorCommutativity.quotientRepEquiv._proof_1
Langlands.Classification.TwoFactorCommutativity.quotientRepEquiv._proof_2
Langlands.Classification.TwoFactorCommutativity.quotientRepEquiv._proof_3
Langlands.Classification.TwoFactorCommutativity.quotientRepEquiv._proof_4
Langlands.Classification.TwoFactorCommutativity.quotientRepEquiv._proof_5
Langlands.Classification.TwoFactorCommutativity.subrepInclusion
Langlands.Classification.TwoFactorCommutativity.subrepInclusion._proof_1
Langlands.Classification.TwoFactorCommutativity.subrepInclusion._proof_2
Langlands.Classification.adjacentSwap_zero_eq_revPerm
Langlands.Classification.adjacentSwap_zero_eq_revPerm._proof_1
Langlands.Classification.adjacentSwap_zero_eq_revPerm._proof_1_1
Langlands.Classification.twoFactorProductConstituentCommutativity
Langlands.Classification.twoFactorProductConstituentCommutativity_of_finiteLength
Langlands.Classification.twoFactorProductConstituentCommutativity_of_finiteLength._proof_1_1
_private.Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof.0.Langlands.Classification.TwoFactorCommutativity.gelfandKazhdanOfTopology
```

### `Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityStatement`

```text
Langlands.Classification.TwoFactorProductConstituentCommutativity
Langlands.Classification.TwoFactorProductConstituentCommutativity._proof_1
Langlands.Classification.TwoFactorProductConstituentCommutativity._proof_2
```
