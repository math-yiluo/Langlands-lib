# Homogeneous multiplicativity of the support-adjusted GL Aubert operator

Author: Worker 105.

`Langlands.Aubert.adjustedHomogeneousMultiplicativity.{uF,uV}` proves the
published proposition
`Langlands.Aubert.AdjustedHomogeneousMultiplicativityStatement.{uF,uV} F T hx`.
The outer data are an arbitrary prime `p`, a supplied
`F : PadicField.{uF} p`, its supplied topological data `T`, and an arbitrary
`hx : BinaryProductExactnessStatement.{uF,uV} F T`. The field and carrier
universes are independent. There are no additional theorem hypotheses.

For every `a b : ℕ` and every two actual exact finite-length Grothendieck
classes `x` of `GL_a(F)` and `y` of `GL_b(F)`, including either rank zero,
the theorem proves

```text
adjustedOperator (a + b) (binaryProductK0 a b x y)
  = binaryProductK0 a b (adjustedOperator a x) (adjustedOperator b y).
```

All maps in this display are the published actual maps with arguments
`F T hx` as appropriate. The proof preserves the target pair and every pair
it imports. The Grothendieck groups retain all actual short exact relations.

## Implemented proof

For positive `a` and `b`, put `B = BlockShape.binary a b ha hb`. The private
construction `refinedInductionJacquetTensorEquiv` combines
`Langlands.RefinedJacquetTensor.jacquetEquiv` with
`Langlands.Parabolic.refinedInductionTensor`. Its source is the actual
normalized refined induction of the actual normalized refined Jacquet module
of a finite external tensor. Its target is the external tensor of the
ordinary normalized induction-after-Jacquet modules in the individual
blocks. The intermediate action uses the inverse actual
`Geometric.refinedLeviEquiv` and the prescribed positive induction and
inverse Jacquet half-moduli. Inflation and twisting of the Jacquet
equivalence give the inducing-action comparison. The induction tensor
theorem supplies the actual smooth-function equivalence.

The private class lemmas apply the published refined K0 generator formulas
to this equivalence. `binaryRefinedTerm` then identifies each binary
refinement term with `productLeviTensorMap` applied to the tensor of its two
ordinary induction-after-Jacquet terms. These are equalities of exact
classes obtained from actual smooth isomorphisms.

`binaryAlternatingTensor` extends this term formula to arbitrary virtual
classes by `TensorProduct.ext` and
`SmoothRep.FiniteLengthGrothendieckGroup.bilinear_ext`. The equivalence
`piFinTwoEquiv` identifies the refinements of the binary shape with
`BlockShape a × BlockShape b`. The exponent
`refinementSignExponent B S` becomes
`(a - (S 0).length) + (b - (S 1).length)`. The identity `pow_add`, together
with the two finite sums and tensor bilinearity, therefore identifies the
Levi alternating operator with the tensor of the two ambient alternating
operators.

`alternatingOperator_binaryProduct_positive` now applies
`Langlands.Aubert.inductionCommutation` to this binary product Levi.
`Langlands.Aubert.productLeviInductionTensorMap_eq` identifies the subsequent
induction map with the actual `binaryProductK0` for the supplied `hx`.
Consequently the unadjusted operators satisfy the positive-rank product
formula on all exact classes. This step identifies the tensor product with
the product-Levi K0 before induction into `GL_(a+b)`.

For the support adjustment, `supportSign_card` proves that any supplied
actual supercuspidal support multiset `s` of an irreducible `π` has
`s.card ≤ n` and gives the sign `(-1)^(n - s.card)`. In positive rank it
unpacks that actual support presentation, applies
`Langlands.CuspidalSupport.glCuspidalTensor` to its supercuspidal factors,
and applies `Langlands.Aubert.supportSign_of_support` to their irreducible
quasicuspidal external tensor. At rank zero the supplied support is empty
and `supportSign_rankZero` gives one.

For two irreducibles `X` and `Y`, actual supercuspidal support presentations
are supplied by
`Langlands.Aubert.SupportGrading.isSupercuspidalSupport_supercuspidalSupport'`.
The theorem
`Langlands.PadicField.TopologicalData.binaryProductConstituentSupport`
gives the sum of these two multisets as a support of **each** irreducible
subquotient of their actual binary product. Cardinality addition, the two
cardinality bounds, and `pow_add` show that every such constituent has sign
`supportSign X * supportSign Y`.

`adjustedOperator_of_constituentSign` expands an actual finite-length class
through its actual Jordan–Hölder composition factors and the inverse
factor-count/realization maps. The support criterion
`mem_support_compositionFactors_iff_isSubquotient` allows the sign formula
on each constituent to be used term by term. Thus a constant constituent
sign factors out of `adjustedOperator` as that sign times
`alternatingOperator`. Combining this with the unadjusted product formula
and `adjustedOperator_irreducible` proves the positive-rank adjusted identity
on irreducible pairs. Double induction using
`SupportGrading.induction_irreducible` extends it to all exact classes by
addition and negation.

The two zero-rank cases use
`Langlands.Aubert.GradedAssociativityProof.rankZero_induction`: every exact
`GL_0` class is an integral combination of the class of the actual unit
line. The actual left and right unit identities for
`gradedMultiplication` imply that the graded adjusted additive map commutes
with multiplication by any such class. The homogeneous formula for
`gradedAdjustedOperator`, injectivity of the homogeneous direct-sum
inclusion, and `adjustedOperator_rankZero` give the required rankwise
identity. This also covers `(a,b) = (0,0)`.

## Main declaration dependencies

Names in this table have prefix `Langlands.`.

| Role | Published declarations |
| --- | --- |
| Refined tensor comparison | `RefinedJacquetTensor.jacquetEquiv`; `Parabolic.refinedInductionTensor`; `Induction.smoothInducedEquiv`; `twistEquiv` |
| Exact class formulas | `Parabolic.normalizedRefinedJacquetK0_finiteLengthClass`; `Parabolic.normalizedRefinedInductionK0_finiteLengthClass`; `Parabolic.normalizedJacquetK0_finiteLengthClass`; `Parabolic.normalizedInductionK0_finiteLengthClass`; `SmoothRep.FiniteLengthGrothendieckGroup.ofObject_eq_of_iso` |
| Positive product and Levi sum | `Aubert.productLeviTensorPrerequisites`; `Aubert.productLeviTensorMap_classes`; `Aubert.alternatingOperatorOnLevi_apply`; `Aubert.alternatingOperator_apply`; `Aubert.inductionCommutation`; `Aubert.productLeviInductionTensorMap_eq` |
| Constituent support and signs | `CuspidalSupport.glCuspidalTensor`; `Aubert.SupportGrading.isSupercuspidalSupport_supercuspidalSupport'`; `PadicField.TopologicalData.binaryProductConstituentSupport`; `Aubert.supportSign_of_support`; `Aubert.supportSign_rankZero`; `Aubert.adjustedOperator_irreducible` |
| Jordan–Hölder extension | `SmoothRep.IrreducibleGrothendieckProof.factorMap_ofRepresentation`; `SmoothRep.IrreducibleGrothendieckProof.realize_comp_factorMap`; `SmoothRep.IrreducibleOperator.mem_support_compositionFactors_iff_isSubquotient`; `SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass`; `Aubert.SupportGrading.induction_irreducible` |
| Zero ranks | `Aubert.GradedAssociativityProof.rankZero_induction`; `Aubert.gradedMultiplication_unit_left`; `Aubert.gradedMultiplication_unit_right`; `Aubert.gradedMultiplication_homogeneous`; `Aubert.gradedAdjustedOperator_homogeneous`; `Aubert.adjustedOperator_rankZero` |

The complete unapplied closing constant has been checked against the full
target telescope, including the independent universe levels and arbitrary
`hx`. Development compilation and Lake inspection report only
`propext`, `Classical.choice`, and `Quot.sound`.

## Provenance and source convention

This is a proof of an existing proposition and an internal assembly of the
published actual representation constructions and identities. The original
source is Anne-Marie Aubert, *Dualité dans le groupe de Grothendieck de la
catégorie des représentations lisses de longueur finie d'un groupe réductif
p-adique*, Transactions of the AMS 347 (1995), 2179–2189; registered source
`aubert-1995-duality`, SHA-256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
The relevant locations are Theorem 1.7(2), printed p.2181; the product
paragraph and Definition 2.1, printed p.2184; and Theorem 2.3, printed p.2185.
These original pages were read, and p.2184 was also visually inspected.

The two corrections recorded in the public Aubert source notes apply:
the tensor product is the K0 of the product Levi, and the induction identity
is Theorem 1.7(2). The support adjustment is essential. The source's defective
Proposition 3.2 is not reapplied here; the already published actual
support-sign and irreducible-image development is used through its named
declarations. This proof establishes the homogeneous multiplicativity
input to Theorem 2.3; it does not assemble that theorem's other conclusions.

## Transitive Classification-origin inventory

Classification is permitted by this task, and the proof uses declarations
originating in Classification modules. In particular, actual support
existence reaches `Langlands.glSupercuspidalEmbedding`; the rank-zero
support construction reaches the dimension-one and unit-isomorphism results
listed below. The imported actual functor, finite-length and induction
commutation results also reach the finite-length, irreducible product
embedding, and two-factor constituent commutativity results below.

The following exhaustive inventory was computed from the closing theorem by
recursively following **both types and values**, including opaque theorem
values, through Lean's `Expr.getUsedConstants`. It retains exactly constants
whose defining module begins `Langlands.Representation.Classification.`.
The traversal visits 83,617 constants in all and retains 166 constants from
21 Classification modules: 130 theorem constants, 34 definitions and two
inductive/constructor constants. Generated helpers and private constants
are included under their exact Lean names. This is a declaration dependency
inventory, not the larger import closure.

### Langlands.Representation.Classification.ConstituentRelations

```text
Langlands.Classification.IsIrreducibleSubrepresentation
```

### Langlands.Representation.Classification.FiniteLengthProof

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

### Langlands.Representation.Classification.IrreducibleProductEmbedding

```text
Langlands.Classification.irreducibleProductEmbedding
Langlands.Classification.irreducibleProduct_embedding
Langlands.Classification.irreducible_supercuspidalProduct_embedding
Langlands.Classification.normalizedProduct_embedding_of_factor_embeddings
Langlands.FiniteTensor.externalMap_injective
```

### Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement

```text
Langlands.Classification.IrreducibleProductEmbeddingTheorem
```

### Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof

```text
Langlands.Classification.irreducibleProductFiniteLength
_private.Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof.0.Langlands.Classification.flattenSupercuspidalFactors
_private.Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof.0.Langlands.Classification.flattenSupercuspidalFactors_obj
```

### Langlands.Representation.Classification.NormalizedProductFiniteLengthProof

```text
Langlands.Classification.ProductLengthProof.finiteLength_of_injective
Langlands.Classification.ProductLengthProof.finiteLength_of_range_eq_ker
Langlands.Classification.ProductLengthProof.finiteLength_of_surjective
Langlands.Classification.ProductLengthProof.irreducibleLevi
Langlands.Classification.ProductLengthProof.leviPreservation
Langlands.Classification.ProductLengthProof.selfMatching_of_finiteLength
Langlands.Classification.ProductLengthProof.step
Langlands.Classification.admissibleFiniteLengthProductPreservation
Langlands.Classification.normalizedInductionFiniteLength
```

### Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement

```text
Langlands.Classification.AdmissibleFiniteLengthProductPreservation
Langlands.Classification.IrreducibleProductFiniteLength
```

### Langlands.Representation.Classification.ProductLeviMinimalIndex

```text
Langlands.ProductLeviMinimalIndex.blockIndex_eq_flatten
Langlands.ProductLeviMinimalIndex.blockIndex_flatten_index
Langlands.ProductLeviMinimalIndex.blockIndex_flatten_index_eq_iff
Langlands.ProductLeviMinimalIndex.blockIndex_flatten_index_ne
Langlands.ProductLeviMinimalIndex.blockIndex_flatten_index_ne._simp_1_1
Langlands.ProductLeviMinimalIndex.blockWeyl_flatten_le
```

### Langlands.Representation.Classification.SegmentHeadSupportCons

```text
Langlands.Classification.SegmentHeadSupport.finrank_eq_one_of_isIrreducible
```

### Langlands.Representation.Classification.SegmentHeadSupportGeneric

```text
Langlands.Classification.SegmentHeadSupport.isSubquotient_refl
```

### Langlands.Representation.Classification.SegmentProductOrderedAssembly

```text
Langlands.Classification.SegmentProductOrderedAssembly.nonempty_iso_unit
```

### Langlands.Representation.Classification.Segments

```text
Langlands.PadicField.TopologicalData.CuspidalDatum
Langlands.PadicField.TopologicalData.CuspidalDatum.IsRepresentedBy
Langlands.PadicField.TopologicalData.CuspidalDatum.cls
Langlands.PadicField.TopologicalData.CuspidalDatum.mk
Langlands.PadicField.TopologicalData.CuspidalDatum.rank
Langlands.PadicField.TopologicalData.CuspidalDatum.rank_pos
```

### Langlands.Representation.Classification.Supercuspidal

```text
Langlands.GeneralLinear.BlockShape.conjugateUnipotent
Langlands.GeneralLinear.IsSupercuspidal
Langlands.GeneralLinear.SupercuspidalClass
Langlands.GeneralLinear.SupercuspidalRep
Langlands.GeneralLinear.SupercuspidalRep.isoClass
Langlands.GeneralLinear.isSupercuspidal_of_equiv
Langlands.GeneralLinear.supercuspidalProperty
Langlands.Jacquet.coinvariantsEquiv
Langlands.Jacquet.coinvariantsEquiv._proof_1
Langlands.Jacquet.coinvariantsEquiv._proof_2
Langlands.Jacquet.coinvariantsEquiv._proof_3
Langlands.Jacquet.coinvariantsEquiv._proof_4
Langlands.Jacquet.coinvariants_subsingleton_iff
```

### Langlands.Representation.Classification.SupercuspidalContragredientAux

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

### Langlands.Representation.Classification.SupercuspidalEmbeddingProof

```text
Langlands.glSupercuspidalEmbedding
```

### Langlands.Representation.Classification.SupercuspidalEmbeddingTransport

```text
Langlands.PadicField.TopologicalData.exists_cuspidalSubrepresentation_of_levi_equiv
Langlands.PadicField.TopologicalData.exists_cuspidalSubrepresentation_of_product_embedding
```

### Langlands.Representation.Classification.SupercuspidalSupport

```text
Langlands.PadicField.TopologicalData.IsCuspidalConstituent
Langlands.PadicField.TopologicalData.IsCuspidalSubrepresentation
Langlands.PadicField.TopologicalData.IsCuspidalSubrepresentation.isCuspidalConstituent
Langlands.PadicField.TopologicalData.IsSupercuspidalSupport
Langlands.PadicField.TopologicalData.IsSupercuspidalSupport.sum_rank
Langlands.PadicField.TopologicalData.cuspidalProductInduced
Langlands.PadicField.TopologicalData.cuspidalShape
Langlands.PadicField.TopologicalData.cuspidalShape._proof_1
Langlands.PadicField.TopologicalData.isSupercuspidalSupport_supercuspidalSupport
Langlands.PadicField.TopologicalData.supercuspidalSupport
Langlands.SmoothRep.IsQuotient.isSubquotient
Langlands.SmoothRep.IsSubquotient.of_iso_right
Langlands.SmoothRep.IsSubrepresentation.isSubquotient
Langlands.SmoothRep.hom_hom_injective
Langlands.SmoothRep.hom_hom_surjective
Langlands.SmoothRep.isSubquotient_iff_exists
Langlands.SmoothRep.isSubquotient_iff_exists.match_1_1
```

### Langlands.Representation.Classification.SupercuspidalSupportStatement

```text
Langlands.GLSupercuspidalEmbeddingStatement
```

### Langlands.Representation.Classification.SupercuspidalTwist

```text
Langlands.GeneralLinear.BlockShape.determinant_eq_one_of_mem_unipotentSubgroup
```

### Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof

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

### Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityStatement

```text
Langlands.Classification.TwoFactorProductConstituentCommutativity
Langlands.Classification.TwoFactorProductConstituentCommutativity._proof_1
Langlands.Classification.TwoFactorProductConstituentCommutativity._proof_2
```
