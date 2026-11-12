# Aubert 1995 Theorem 2.3 for the support-adjusted GL Aubert operator

Author: Worker 186.

`Langlands.Aubert.aubertTheorem23.{uF, uV} F T hx hl hp` proves exactly the
published `Langlands.Aubert.AubertTheorem23Statement.{uF, uV} F T hx hl hp`
from `Langlands.Representation.Aubert.ZelevinskyComparison`. Its only
parameters are those of the proposition: a prime `p` with `[Fact p.Prime]`,
`F : PadicField.{uF} p`, `T : F.TopologicalData` and the three explicit
proposition parameters

- `hx : Langlands.Aubert.BinaryProductExactnessStatement F T`,
- `hl : Langlands.Aubert.GradedInductionRingLawsStatement F T hx`, and
- `hp : Langlands.Aubert.SegmentPolynomialComparisonStatement F T hx hl`.

The universes `uF` and `uV` are independent. The theorem holds for every value
of `hx`, `hl` and `hp`; it adds no hypothesis. The target pair and every pair
it imports are unchanged.

The proposition is the conjunction of three statements about the direct sum,
over all natural ranks including zero, of the actual exact finite-length
Grothendieck groups of `GL_n(F)`, with the actual induction product:

1. `AdjustedMultiplicativityStatement F T hx`: the graded additive extension
   of `adjustedOperator` is multiplicative on every graded class;
2. `ZelevinskyInvolutivityStatement F T hx hl hp`: the constructed
   `zelevinskyEndomorphism F T hx hl hp` is an involution;
3. `AubertZelevinskyComparisonStatement F T hx hl hp`:
   `gradedAdjustedOperator F T` equals the integer-linear map underlying
   `zelevinskyEndomorphism F T hx hl hp` on the whole graded group.

## Implemented proof

Unqualified project names below are in `Langlands.Aubert`. The proof first
installs
`T.topology` and the ring structure `gradedInductionRing F T hx hl` as
local instances, as the target module does.

*Multiplicativity.* `adjustedHomogeneousMultiplicativity F T hx` proves
`AdjustedHomogeneousMultiplicativityStatement F T hx`, which is the
homogeneous condition `HomogeneousOperatorMultiplicativityStatement` for the
family `adjustedOperator F T`. The published bilinear extension
`gradedOperator_multiplicative_of_homogeneous` turns it into
`GradedOperatorMultiplicativityStatement F T (adjustedOperator F T) hx`. By
definition this is `AdjustedMultiplicativityStatement F T hx`, the first
conjunct. Call this proof `hm`.

*Comparison.* `gradedOperatorRingHom_eq_zelevinsky` takes `hp`, `hm`, unit
preservation and the segment exchange. It states that the ring endomorphism
`gradedOperatorRingHom F T (adjustedOperator F T) hx hl hm hu` equals
`zelevinskyEndomorphism F T hx hl hp`. Unit preservation is
`gradedAdjustedOperator_unit F T`, and the segment exchange is
`adjustedSegmentExchange F T`, a proof of
`AdjustedSegmentExchangeStatement F T`. That statement is by definition
`GradedOperatorSegmentExchangeStatement F T (adjustedOperator F T)`. The
underlying function of `gradedOperatorRingHom` is by definition
`gradedOperator F T (adjustedOperator F T)`, which is
`gradedAdjustedOperator F T`. So `RingHom.congr_fun` applied to this equality
gives, for every graded class `y`,
`gradedAdjustedOperator F T y = zelevinskyEndomorphism F T hx hl hp y`. Call
this pointwise identity `hy`. `LinearMap.ext hy` proves the third conjunct,
because the right-hand side of `AubertZelevinskyComparisonStatement` is the
`toIntLinearMap` of the additive map underlying the same ring endomorphism.

*Involutivity.* For a graded class `x`, rewriting both applications of
`zelevinskyEndomorphism F T hx hl hp` back to `gradedAdjustedOperator F T`
with `hy` reduces the second conjunct to
`gradedAdjustedOperator F T (gradedAdjustedOperator F T x) = x`. This is
`adjustedInvolutivity F T x`, the published proof of
`AdjustedInvolutivityStatement F T`.

Apart from naming `zelevinskyEndomorphism F T hx hl hp`, the proof uses the
polynomial comparison `hp` only as an argument of
`gradedOperatorRingHom_eq_zelevinsky`. That theorem compares two ring
endomorphisms through the polynomial universal property: both agree after
composition with `segmentPolynomialEquiv F T hx hl hp`, because they agree on
the segment variables. No calculation on individual segment generators alone
is used to obtain the whole-ring equality.

## Declaration-level dependencies

The proof body names these project declarations, all in `Langlands.Aubert`
except the first:

- `Langlands.PadicField.TopologicalData.topology` (as `T.topology`) and
  `gradedInductionRing`
  (module `Langlands.Representation.Aubert.GradedGrothendieck`), installed
  as local instances;
- `adjustedHomogeneousMultiplicativity`
  (module `Langlands.Representation.Aubert.AdjustedHomogeneousMultiplicativityProof`);
- `adjustedSegmentExchange`
  (module `Langlands.Representation.Aubert.AdjustedSegmentExchangeProof`);
- `adjustedInvolutivity`
  (module `Langlands.Representation.Aubert.AdjustedInvolutivityProof`);
- `gradedOperator_multiplicative_of_homogeneous` and
  `gradedOperatorRingHom_eq_zelevinsky`
  (module `Langlands.Representation.Aubert.GradedOperatorComparison`);
- `gradedAdjustedOperator_unit`, `gradedAdjustedOperator`,
  `AdjustedMultiplicativityStatement` and `AubertTheorem23Statement`
  (module `Langlands.Representation.Aubert.ZelevinskyComparison`);
- `adjustedOperator` (module `Langlands.Representation.Aubert.SupportSign`);
- `zelevinskyEndomorphism`
  (module `Langlands.Representation.Aubert.ZelevinskyPolynomial`).

The only non-project lemmas used directly are Mathlib's `RingHom.congr_fun`
and `LinearMap.ext`. The module imports the three proof modules listed above;
they import `ZelevinskyComparison`.

Lean compilation and declaration inspection in the task's environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` succeeded with no errors and no
warnings. The theorem has level parameters `uF, uV`, and its axioms are
exactly `propext`, `Classical.choice` and `Quot.sound`. A private check also
rebuilt the full dependent telescope of the statement's type,
`∀ {p} [Fact p.Prime] F T hx hl hp, AubertTheorem23Statement F T hx hl hp`.
It confirmed that this expression is structurally equal to the type of
`@aubertTheorem23.{uF, uV}`.

## Source and provenance

The source is A.-M. Aubert, *Dualité dans le groupe de Grothendieck de la
catégorie des représentations lisses de longueur finie d'un groupe réductif
p-adique*, Trans. Amer. Math. Soc. 347, no. 6 (1995). The involution `D` is
given by Definition 2.1, and Remark 2.2 records its segment formula; both are
on printed p.2184. Theorem 2.3 on printed p.2185 states that `D` coincides
with Zelevinsky's involution. The registered source is
`aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`, and
pp.2184–2185 were read directly. As Aubert recalls on p.2185, Zelevinsky's
involution (Zelevinsky 1980, §9.12) is the unique ring endomorphism
extending the segment exchange on the polynomial generators of Zelevinsky's
Corollary 7.5.

The Lean proof has the same structure as Aubert's argument on p.2185. The ring
is a polynomial ring in the segment classes, so two ring endomorphisms that
agree on segments agree everywhere. In Lean, the polynomial-comparison parameter `hp`
supplies this structure, `adjustedHomogeneousMultiplicativity` makes `D` a
ring endomorphism, and `adjustedSegmentExchange` supplies the segment values.
The Library also proves the three parameters (`binaryProductExactness`,
`gradedInductionRingLaws` and `segmentPolynomialComparison`). The target keeps
them as explicit parameters, and this proof does not use those theorems.
Aubert computes the segment values directly, using Definition 1.5 and
Zelevinsky's Propositions 3.4 and 9.13. The Lean input instead derives them
from the published signed segment exchange and the effective support sign.
Involutivity of Zelevinsky's endomorphism (§9.12) is obtained here from
involutivity of the additive adjusted operator. This new module is internal
assembly of published Lean results; it introduces no new definition and no
new mathematical input.

## Transitive classification dependencies

Classification is permitted by this task, and the proof reaches results
defined in classification modules through its published inputs. This
contribution makes no claim of classification independence.

A private development diagnostic recursively traversed the final theorem's
type and proof value, then the types and values of every reached project
declaration, including opaque values, inductive constructors and recursors.
It used Lean's `Expr.getUsedConstants`. Non-project constants were not
expanded, since they cannot depend on project results. The diagnostic ran
against the workspace Library base `c6e80146c42a1f62d41f90e444f503ccf17f4d20`
plus this module. The traversal reached 10,344 project constants in 869
project modules. Of these, 437 constants (321 theorem constants) are defined
in 58 modules under `Langlands.Representation.Classification`.

The same traversal from individual roots shows where these come from:

- The target statement's own type reaches 353 of them. This happens through
  the definitions it unfolds to, such as the actual segment classes, the
  support sign inside `adjustedOperator`, and the actual graded product.
  This set includes `Langlands.Classification.segmentZelevinskyConstituentExistence`,
  `Langlands.Classification.segmentSpecialConstituentExistence`,
  `Langlands.Classification.normalizedInductionFiniteLength`,
  `Langlands.Classification.irreducibleProductFiniteLength`,
  `Langlands.Classification.irreducibleProductEmbedding`,
  `Langlands.Classification.admissibleFiniteLengthProductPreservation`,
  `Langlands.Classification.commonImageMultiplicityOne`,
  `Langlands.Classification.cuspidalIntegralTwistFreeness`,
  `Langlands.Classification.segmentInductionAdmissibility`,
  `Langlands.Classification.segmentJacquetMultiplicityReduction`,
  `Langlands.Classification.segmentFactors_isIrreducible_isLeviCuspidal`,
  `Langlands.Classification.segmentFactors_associated_segmentFactorsDown`,
  `Langlands.Classification.twoFactorProductConstituentCommutativity`,
  `Langlands.Classification.unequalIrreducibleQuotientKernels`,
  `Langlands.Parabolic.normalizedJacquetFiniteLength`,
  `Langlands.glCuspidalJacquetMultiplicityPrerequisites`,
  `Langlands.glOppositeCuspidalJacquetFiltrationFromUpper`,
  `Langlands.glUpperCuspidalJacquetMultiplicityFromFiltration`,
  `Langlands.oppositeJacquetQuotientDetection` and
  `Langlands.upperJacquetSubrepresentationDetection`.
- `adjustedHomogeneousMultiplicativity` reaches 166, of which 17 are reached
  by no other input or by the statement type. Among these are
  `Langlands.glSupercuspidalEmbedding` and its statement
  `Langlands.GLSupercuspidalEmbeddingStatement`, used for actual
  supercuspidal-support existence, as well as
  `Langlands.PadicField.TopologicalData.supercuspidalSupport` and
  `Langlands.Classification.SegmentProductOrderedAssembly.nonempty_iso_unit`.
- `adjustedSegmentExchange` reaches 417, of which 60 are reached by no
  other input or by the statement type. These are mainly the segment
  full-Jacquet, head and socle helpers (`Langlands.SegmentFullJacquet.*`,
  `Langlands.Classification.head`, `Langlands.Classification.socleEquivOfInjective`
  and related declarations).
- `adjustedInvolutivity` and `gradedAdjustedOperator_unit` each reach 137.
  Beyond the statement type, both reach only the six
  `Langlands.ProductLeviMinimalIndex` constants listed below. These are also
  reached by `adjustedHomogeneousMultiplicativity`.
- `gradedOperator_multiplicative_of_homogeneous` and
  `gradedOperatorRingHom_eq_zelevinsky` reach nothing beyond the statement
  type.

The union over the statement type and the three proof inputs is the whole
inventory; the assembly in this module adds no further classification
constant.

The complete inventory follows. It conservatively records every reached
constant whose defining module is under
`Langlands.Representation.Classification`. That includes definitions,
statement predicates, generated proof helpers and private helpers, listed
under their exact Lean names. Module membership alone does not make a
declaration a classification theorem. This is a declaration-use inventory,
not the larger import closure.

### `Langlands.Representation.Classification.CanonicalConstituents`

```text
Langlands.Classification.HasIrreducibleHead
Langlands.Classification.HasIrreducibleSocle
Langlands.Classification.IsIrreducibleHead.headKernel_eq
Langlands.Classification.IsIrreducibleHead.nonempty_headEquiv
Langlands.Classification.IsIrreducibleSocle.nonempty_socleEquiv
Langlands.Classification.IsIrreducibleSocle.socle_eq
Langlands.Classification.head
Langlands.Classification.headEquivOfSurjective
Langlands.Classification.headEquivOfSurjective._proof_1
Langlands.Classification.headEquivOfSurjective._proof_2
Langlands.Classification.headEquivOfSurjective._proof_3
Langlands.Classification.headEquivOfSurjective._proof_4
Langlands.Classification.headEquivOfSurjective._proof_5
Langlands.Classification.headKernel
Langlands.Classification.headKernel._proof_1
Langlands.Classification.headKernel._proof_2
Langlands.Classification.headKernel._proof_3
Langlands.Classification.headKernel._proof_4
Langlands.Classification.headKernel_le_ker
Langlands.Classification.headKernel_stable
Langlands.Classification.irreducibleImages
Langlands.Classification.ofSocle._proof_1
Langlands.Classification.range_le_socle
Langlands.Classification.socle
Langlands.Classification.socle._proof_1
Langlands.Classification.socleEquivOfInjective
Langlands.Classification.socleEquivOfInjective._proof_1
Langlands.Classification.socleEquivOfInjective._proof_2
Langlands.Classification.socleEquivOfInjective._proof_3
Langlands.Classification.socleRepresentation
Langlands.Classification.toHead._proof_1
```

### `Langlands.Representation.Classification.CommonImageMultiplicityOneProof`

```text
Langlands.Classification.commonImageMultiplicityOne
Langlands.Classification.commonImageMultiplicityOne._proof_1_1
_private.Langlands.Representation.Classification.CommonImageMultiplicityOneProof.0.Langlands.Classification.irreducible_carrier_nontrivial
_private.Langlands.Representation.Classification.CommonImageMultiplicityOneProof.0.Langlands.Classification.positive_zero_composite_impossible
_private.Langlands.Representation.Classification.CommonImageMultiplicityOneProof.0.Langlands.Classification.positive_zero_composite_impossible._proof_1_1
```

### `Langlands.Representation.Classification.CommonImageMultiplicityOneStatement`

```text
Langlands.Classification.CommonImageMultiplicityOneStatement
```

### `Langlands.Representation.Classification.ConstituentRelations`

```text
Langlands.Classification.HasScalarCharacter
Langlands.Classification.IsIrreducibleHead
Langlands.Classification.IsIrreducibleSocle
Langlands.Classification.IsIrreducibleSubrepresentation
```

### `Langlands.Representation.Classification.Cosocle`

```text
Langlands.Classification.isIrreducible_iff_isCoatom_ker
```

### `Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof`

```text
Langlands.Classification.IntegralTwistFreeness.character_eq_one_on_center
Langlands.Classification.IntegralTwistFreeness.exponent_eq_zero_of_equiv
Langlands.Classification.IntegralTwistFreeness.scalar_uniformizer_value
Langlands.Classification.cuspidalIntegralTwistFreeness
```

### `Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement`

```text
Langlands.Classification.CuspidalIntegralTwistFreeness
```

### `Langlands.Representation.Classification.CuspidalJacquetFunctorExactnessProof`

```text
Langlands.CuspidalJacquetMultiplicity.oppositeFunctor_additive
Langlands.CuspidalJacquetMultiplicity.oppositeFunctor_preservesEpimorphisms
Langlands.CuspidalJacquetMultiplicity.oppositeFunctor_preservesMonomorphisms
Langlands.CuspidalJacquetMultiplicity.oppositeUnipotent_finite_containment
Langlands.CuspidalJacquetMultiplicity.upperFunctor_additive
Langlands.CuspidalJacquetMultiplicity.upperFunctor_preservesEpimorphisms
Langlands.CuspidalJacquetMultiplicity.upperFunctor_preservesMonomorphisms
```

### `Langlands.Representation.Classification.CuspidalJacquetFunctors`

```text
Langlands.CuspidalJacquetMultiplicity.oppositeFunctor
Langlands.CuspidalJacquetMultiplicity.oppositeFunctor._proof_1
Langlands.CuspidalJacquetMultiplicity.oppositeFunctor._proof_2
Langlands.CuspidalJacquetMultiplicity.oppositeMap
Langlands.CuspidalJacquetMultiplicity.oppositeMap._proof_1
Langlands.CuspidalJacquetMultiplicity.oppositeMap._proof_2
Langlands.CuspidalJacquetMultiplicity.oppositeMap._proof_3
Langlands.CuspidalJacquetMultiplicity.oppositeMap._proof_4
Langlands.CuspidalJacquetMultiplicity.oppositeMap._proof_5
Langlands.CuspidalJacquetMultiplicity.upperFunctor
Langlands.CuspidalJacquetMultiplicity.upperFunctor._proof_1
Langlands.CuspidalJacquetMultiplicity.upperFunctor._proof_2
```

### `Langlands.Representation.Classification.CuspidalJacquetMultiplicityProof`

```text
Langlands.glCuspidalJacquetMultiplicityPrerequisites
```

### `Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement`

```text
Langlands.CuspidalJacquetMultiplicity.induced
Langlands.CuspidalJacquetMultiplicity.induced._proof_1
Langlands.CuspidalJacquetMultiplicity.oppositeJacquet
Langlands.CuspidalJacquetMultiplicity.oppositeJacquet._proof_1
Langlands.CuspidalJacquetMultiplicity.oppositeJacquet._proof_2
Langlands.CuspidalJacquetMultiplicity.upperJacquet
Langlands.CuspidalJacquetMultiplicity.upperJacquet._proof_1
Langlands.GLCuspidalJacquetMultiplicityPrerequisitesStatement
Langlands.GLCuspidalJacquetMultiplicityStatement
```

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

### `Langlands.Representation.Classification.HeadQuotientCriterionProof`

```text
Langlands.Classification.unequalIrreducibleQuotientKernels
Langlands.Classification.unequalIrreducibleQuotientKernels._abel_1_1
```

### `Langlands.Representation.Classification.HeadQuotientCriterionStatement`

```text
Langlands.Classification.UnequalIrreducibleQuotientKernelsStatement
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

### `Langlands.Representation.Classification.MultiplicityOneConstituentProof`

```text
Langlands.Classification.mappedProductSplitting
Langlands.Classification.multiplicityOneHeadCore
Langlands.Classification.multiplicityOneHeadCore._proof_1_1
Langlands.Classification.multiplicityOneSocleCore
Langlands.Classification.multiplicityOneSocleCore._proof_1_1
Langlands.Classification.smoothProduct
Langlands.Classification.smoothProduct._proof_1
_private.Langlands.Representation.Classification.MultiplicityOneConstituentProof.0.Langlands.Classification.isAtom_embedding_range
```

### `Langlands.Representation.Classification.NormalizedProductFiniteLengthProof`

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

### `Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement`

```text
Langlands.Classification.AdmissibleFiniteLengthProductPreservation
Langlands.Classification.IrreducibleProductFiniteLength
```

### `Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof`

```text
Langlands.OppositeCuspidalJacquetFiltration.conjugatesLevi_reverse
Langlands.OppositeCuspidalJacquetFiltration.isMinimalRepresentative_reverse_inv_mul
Langlands.OppositeCuspidalJacquetFiltration.isMinimalRepresentative_reverse_mul
Langlands.OppositeCuspidalJacquetFiltration.leviConjugation_symm_leviReverseEquiv
Langlands.OppositeCuspidalJacquetFiltration.leviConjugation_symm_leviReverseEquiv._simp_1_1
Langlands.OppositeCuspidalJacquetFiltration.leviConjugation_symm_leviReverseEquiv._simp_1_4
Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv
Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_1
Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_10
Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_2
Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_3
Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_4
Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_5
Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_6
Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_7
Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_8
Langlands.OppositeCuspidalJacquetFiltration.minimalReverseEquiv._proof_9
Langlands.OppositeCuspidalJacquetFiltration.oppositeJacquetReverseEquiv
Langlands.OppositeCuspidalJacquetFiltration.oppositeJacquetReverseEquiv._proof_1
Langlands.OppositeCuspidalJacquetFiltration.oppositeJacquetReverseEquiv._proof_2
Langlands.OppositeCuspidalJacquetFiltration.reverseCoinvariantsEquiv
Langlands.OppositeCuspidalJacquetFiltration.reverseCoinvariantsEquiv._proof_1
Langlands.OppositeCuspidalJacquetFiltration.reverseCoinvariantsEquiv._proof_2
Langlands.OppositeCuspidalJacquetFiltration.reverseCoinvariantsEquiv._proof_3
Langlands.OppositeCuspidalJacquetFiltration.reverseCoinvariantsEquiv._proof_4
Langlands.OppositeCuspidalJacquetFiltration.reverseCoinvariantsEquiv._proof_5
Langlands.OppositeCuspidalJacquetFiltration.reverseCoinvariantsEquiv._proof_6
Langlands.OppositeCuspidalJacquetFiltration.reverseJacquetEquiv
Langlands.OppositeCuspidalJacquetFiltration.reverseJacquetEquiv._proof_1
Langlands.OppositeCuspidalJacquetFiltration.reverseJacquetEquiv_mk
Langlands.OppositeCuspidalJacquetFiltration.reversePermutation_lt_of_blockIndex_eq
Langlands.OppositeCuspidalJacquetFiltration.reversePermutation_symm_index_strictMono
Langlands.OppositeCuspidalJacquetFiltration.transportReverseEquiv
Langlands.OppositeCuspidalJacquetFiltration.transportReverseEquiv._proof_1
Langlands.OppositeCuspidalJacquetFiltration.transportReverseEquiv._proof_2
Langlands.glOppositeCuspidalJacquetFiltrationFromUpper
```

### `Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationStatement`

```text
Langlands.GLOppositeCuspidalJacquetFiltrationFromUpperStatement
Langlands.GLOppositeCuspidalJacquetFiltrationFromUpperStatement._proof_1
```

### `Langlands.Representation.Classification.OppositeJacquetQuotientDetectionProof`

```text
Langlands.oppositeJacquetQuotientDetection
```

### `Langlands.Representation.Classification.OppositeJacquetQuotientDetectionStatement`

```text
Langlands.OppositeJacquetQuotientDetectionStatement
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

### `Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof`

```text
Langlands.Classification.hasScalarCharacter_twist
Langlands.PadicField.TopologicalData.coe_determinantPowerCharacter_scalar
Langlands.PadicField.TopologicalData.hasScalarCharacter_segmentFactor
```

### `Langlands.Representation.Classification.SegmentConstituentStatement`

```text
Langlands.Classification.SegmentSpecialConstituentExistence
Langlands.Classification.SegmentZelevinskyConstituentExistence
```

### `Langlands.Representation.Classification.SegmentFullJacquetAdjunction`

```text
Langlands.SegmentFullJacquet.exists_jacquet_to_tensor_ne_zero
```

### `Langlands.Representation.Classification.SegmentFullJacquetCentral`

```text
Langlands.SegmentFullJacquet.blockTensor_blockScalarLevi
Langlands.SegmentFullJacquet.digits_sum_injective
Langlands.SegmentFullJacquet.digits_sum_injective._f
Langlands.SegmentFullJacquet.digits_sum_injective.match_1_1
Langlands.SegmentFullJacquet.leviConjugation_symm_blockScalarLevi
Langlands.SegmentFullJacquet.perm_eq_of_weightedSum_eq
Langlands.SegmentFullJacquet.segmentScalar
Langlands.SegmentFullJacquet.segmentScalar_eq
Langlands.SegmentFullJacquet.segmentScalar_injective
Langlands.SegmentFullJacquet.separatingEntries
Langlands.SegmentFullJacquet.transport_blockTensor_blockScalarLevi
Langlands.SegmentFullJacquet.uniformizerAbs
Langlands.SegmentFullJacquet.uniformizerAbs_lt_one
Langlands.SegmentFullJacquet.uniformizerAbs_pos
```

### `Langlands.Representation.Classification.SegmentFullJacquetSplitting`

```text
Langlands.SegmentFullJacquet.blockPerm
Langlands.SegmentFullJacquet.blockPerm._proof_1
Langlands.SegmentFullJacquet.blockPerm_injective
Langlands.SegmentFullJacquet.exists_segmentJacquetFiltration
Langlands.SegmentFullJacquet.separatingScalar
Langlands.SegmentFullJacquet.separatingScalar_comm
Langlands.SegmentFullJacquet.transport_segment_separatingScalar
```

### `Langlands.Representation.Classification.SegmentHeadDecreasingSocle`

```text
Langlands.Classification.IsIrreducibleSocle.nonempty_equiv_of_subrepresentation
Langlands.Classification.IsIrreducibleSocle.of_targetEquiv
Langlands.PadicField.TopologicalData.IsSegmentHead.isIrreducibleSocle_down
Langlands.PadicField.TopologicalData.IsSegmentHead.nonempty_equiv_of_down_jacquet_hom
Langlands.PadicField.TopologicalData.IsSegmentHead.nonempty_equiv_of_down_subrepresentation
```

### `Langlands.Representation.Classification.SegmentHeadSupportCons`

```text
Langlands.Classification.SegmentHeadSupport.finrank_eq_one_of_isIrreducible
```

### `Langlands.Representation.Classification.SegmentHeadSupportGeneric`

```text
Langlands.Classification.SegmentHeadSupport.isSubquotient_refl
```

### `Langlands.Representation.Classification.SegmentInductionAdmissibilityProof`

```text
Langlands.Classification.segmentInductionAdmissibility
```

### `Langlands.Representation.Classification.SegmentInductionAdmissibilityStatement`

```text
Langlands.Classification.SegmentInductionAdmissibilityStatement
```

### `Langlands.Representation.Classification.SegmentJacquetMultiplicityProof`

```text
Langlands.Classification.segmentJacquetMultiplicityReduction
```

### `Langlands.Representation.Classification.SegmentJacquetMultiplicityStatement`

```text
Langlands.Classification.SegmentJacquetMultiplicityReductionStatement
Langlands.Classification.SegmentJacquetMultiplicityReductionStatement._proof_1
```

### `Langlands.Representation.Classification.SegmentJacquetReversal`

```text
Langlands.Classification.segmentTensorDownReverseEquiv
Langlands.Classification.segmentTensorDownReverseEquiv._proof_1
Langlands.Classification.segmentTensorDownReverseEquiv._proof_2
Langlands.Classification.segmentTensorDownReverseEquiv._proof_3
Langlands.Classification.segmentTensorReverseEquiv
Langlands.Classification.segmentTensorReverseEquiv._proof_1
Langlands.Classification.segmentTensorReverseEquiv._proof_2
Langlands.Classification.segmentTensorReverseEquiv._proof_3
Langlands.Classification.segmentTensorReverseEquiv._proof_4
Langlands.Classification.segmentTensorReverseEquiv._proof_5
Langlands.Classification.segmentTensorReverseEquiv._proof_6
Langlands.Classification.segment_opposite_upper_multiplicity_iff
Langlands.Classification.segment_upper_opposite_multiplicity_iff
```

### `Langlands.Representation.Classification.SegmentJacquetSubobject`

```text
Langlands.SegmentFullJacquet.exists_subrepresentationJacquetSeries
Langlands.SegmentFullJacquet.subrepresentationJacquet_isLeviQuasicuspidal
_private.Langlands.Representation.Classification.SegmentJacquetSubobject.0.Langlands.SegmentFullJacquet.subobjectJacquet_injective
_private.Langlands.Representation.Classification.SegmentJacquetSubobject.0.Langlands.SegmentFullJacquet.supercuspidalScalarCharacter
```

### `Langlands.Representation.Classification.SegmentProductOrderedAssembly`

```text
Langlands.Classification.SegmentProductOrderedAssembly.nonempty_iso_unit
```

### `Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof`

```text
Langlands.Classification.segmentSpecialConstituentExistence
_private.Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof.0.Langlands.Classification.segmentSpecialConstituentExistence_of_pointwise
_private.Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof.0.Langlands.Classification.specialSegmentQuotient_admissible
```

### `Langlands.Representation.Classification.SegmentTensorReversalProof`

```text
Langlands.Classification.segmentFactors_associated_segmentFactorsDown
Langlands.Classification.segmentFactors_associated_segmentFactorsDown._proof_1_1
_private.Langlands.Representation.Classification.SegmentTensorReversalProof.0.Langlands.Classification.blockPermutationTensorEquiv
_private.Langlands.Representation.Classification.SegmentTensorReversalProof.0.Langlands.Classification.blockPermutationTensorEquiv._proof_1
_private.Langlands.Representation.Classification.SegmentTensorReversalProof.0.Langlands.Classification.blockPermutationTensorEquiv._proof_2
_private.Langlands.Representation.Classification.SegmentTensorReversalProof.0.Langlands.Classification.blockPermutationTensorEquiv._proof_3
```

### `Langlands.Representation.Classification.SegmentTensorStabilizerProof`

```text
Langlands.Classification.cuspidalDatum_integralTwist_injective
Langlands.Classification.segmentFactorsDown_isIrreducible_isLeviCuspidal
Langlands.Classification.segmentFactorsDown_tensorStabilizer_count
Langlands.Classification.segmentFactorsDown_tensorStabilizer_count._proof_1_1
Langlands.Classification.segmentFactors_isIrreducible_isLeviCuspidal
Langlands.Classification.segmentFactors_tensorStabilizer_count
Langlands.Classification.segmentSupercuspidalFactor
Langlands.Classification.segmentSupercuspidalFactor_datum_injective_nat
```

### `Langlands.Representation.Classification.SegmentZelevinskyConstituentExistenceProof`

```text
Langlands.Classification.segmentZelevinskyConstituentExistence
_private.Langlands.Representation.Classification.SegmentZelevinskyConstituentExistenceProof.0.Langlands.Classification.segmentQuotient_admissible
_private.Langlands.Representation.Classification.SegmentZelevinskyConstituentExistenceProof.0.Langlands.Classification.segmentZelevinskyConstituentExistence_of_pointwise
```

### `Langlands.Representation.Classification.Segments`

```text
Langlands.Classification.IsIrreducibleHead.of_equiv
Langlands.Classification.IsIrreducibleSocle.of_equiv
Langlands.Classification.IsIrreducibleSocle.of_equiv._simp_1_1
Langlands.Classification.IsIrreducibleSubrepresentation.of_equiv
Langlands.GeneralLinear.BlockShape.uniform
Langlands.GeneralLinear.BlockShape.uniform._proof_1
Langlands.GeneralLinear.SupercuspidalClass.twist_congr
Langlands.PadicField.TopologicalData.CuspidalDatum
Langlands.PadicField.TopologicalData.CuspidalDatum.IsRepresentedBy
Langlands.PadicField.TopologicalData.CuspidalDatum.casesOn
Langlands.PadicField.TopologicalData.CuspidalDatum.cls
Langlands.PadicField.TopologicalData.CuspidalDatum.mk
Langlands.PadicField.TopologicalData.CuspidalDatum.mk.inj
Langlands.PadicField.TopologicalData.CuspidalDatum.mk.injEq
Langlands.PadicField.TopologicalData.CuspidalDatum.mk.noConfusion
Langlands.PadicField.TopologicalData.CuspidalDatum.noConfusion
Langlands.PadicField.TopologicalData.CuspidalDatum.noConfusionType
Langlands.PadicField.TopologicalData.CuspidalDatum.rank
Langlands.PadicField.TopologicalData.CuspidalDatum.rank_pos
Langlands.PadicField.TopologicalData.CuspidalDatum.rec
Langlands.PadicField.TopologicalData.CuspidalDatum.twist
Langlands.PadicField.TopologicalData.CuspidalDatum.twist_twist
Langlands.PadicField.TopologicalData.CuspidalDatum.twist_zero
Langlands.PadicField.TopologicalData.IsSegmentHead
Langlands.PadicField.TopologicalData.IsSegmentSocle
Langlands.PadicField.TopologicalData.IsSegmentSocle.isSegmentSubrepresentation
Langlands.PadicField.TopologicalData.IsSegmentSubrepresentation
Langlands.PadicField.TopologicalData.Segment
Langlands.PadicField.TopologicalData.Segment.base
Langlands.PadicField.TopologicalData.Segment.degree
Langlands.PadicField.TopologicalData.Segment.length
Langlands.PadicField.TopologicalData.Segment.length_pos
Langlands.PadicField.TopologicalData.Segment.mk
Langlands.PadicField.TopologicalData.Segment.rank
Langlands.PadicField.TopologicalData.Segment.rank_pos
Langlands.PadicField.TopologicalData.isSegmentHead_iff
Langlands.PadicField.TopologicalData.isSegmentSubrepresentation_iff
Langlands.PadicField.TopologicalData.segmentFactor
Langlands.PadicField.TopologicalData.segmentFactors
Langlands.PadicField.TopologicalData.segmentFactorsDown
Langlands.PadicField.TopologicalData.segmentInduced
Langlands.PadicField.TopologicalData.segmentInducedDown
Langlands.PadicField.TopologicalData.segmentInducedDownIso
Langlands.PadicField.TopologicalData.segmentInducedDownIso._proof_1
Langlands.PadicField.TopologicalData.segmentInducedDownIsoOfRepresented
Langlands.PadicField.TopologicalData.segmentInducedIso
Langlands.PadicField.TopologicalData.segmentInducedIso._proof_1
Langlands.PadicField.TopologicalData.segmentInducedIsoOfRepresented
Langlands.PadicField.TopologicalData.segmentInducedIsoOfRepresented._proof_1
Langlands.PadicField.TopologicalData.supercuspidalClassRealPowerTwist_add
Langlands.PadicField.TopologicalData.supercuspidalClassRealPowerTwist_zero
```

### `Langlands.Representation.Classification.Supercuspidal`

```text
Langlands.GeneralLinear.BlockShape.conjugateUnipotent
Langlands.GeneralLinear.IsSupercuspidal
Langlands.GeneralLinear.SupercuspidalClass
Langlands.GeneralLinear.SupercuspidalRep
Langlands.GeneralLinear.SupercuspidalRep.isoClass
Langlands.GeneralLinear.SupercuspidalRep.isoClass_eq_iff
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

### `Langlands.Representation.Classification.SupercuspidalEmbeddingProof`

```text
Langlands.glSupercuspidalEmbedding
```

### `Langlands.Representation.Classification.SupercuspidalEmbeddingTransport`

```text
Langlands.PadicField.TopologicalData.exists_cuspidalSubrepresentation_of_levi_equiv
Langlands.PadicField.TopologicalData.exists_cuspidalSubrepresentation_of_product_embedding
```

### `Langlands.Representation.Classification.SupercuspidalSupport`

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

### `Langlands.Representation.Classification.SupercuspidalSupportStatement`

```text
Langlands.GLSupercuspidalEmbeddingStatement
```

### `Langlands.Representation.Classification.SupercuspidalTwist`

```text
Langlands.GeneralLinear.BlockShape.conjugateUnipotent_le_ker_determinant
Langlands.GeneralLinear.BlockShape.determinant_eq_one_of_mem_unipotentSubgroup
Langlands.GeneralLinear.SupercuspidalClass.twist
Langlands.GeneralLinear.SupercuspidalClass.twist._proof_1
Langlands.GeneralLinear.SupercuspidalClass.twist.match_1
Langlands.GeneralLinear.SupercuspidalClass.twist_one
Langlands.GeneralLinear.SupercuspidalClass.twist_twist
Langlands.GeneralLinear.SupercuspidalRep.isoMk
Langlands.GeneralLinear.SupercuspidalRep.twist
Langlands.GeneralLinear.SupercuspidalRep.twist._proof_1
Langlands.GeneralLinear.SupercuspidalRep.twistFunctor
Langlands.GeneralLinear.SupercuspidalRep.twistFunctor._proof_1
Langlands.GeneralLinear.isSupercuspidal_twist_iff
Langlands.GeneralLinear.isSupercuspidal_twist_iff_of_le_ker
Langlands.GeneralLinear.ker_determinant_le_ker_comp
Langlands.GeneralLinear.ker_determinant_le_ker_mul
Langlands.GeneralLinear.ker_determinant_le_ker_one
Langlands.Jacquet.subsingleton_coinvariants_twist_iff
Langlands.PadicField.TopologicalData.determinantPowerCharacter
Langlands.PadicField.TopologicalData.isOpen_ker_determinantPowerCharacter
Langlands.PadicField.TopologicalData.ker_determinant_le_ker_determinantPowerCharacter
Langlands.PadicField.TopologicalData.supercuspidalClassRealPowerTwist
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

### `Langlands.Representation.Classification.UpperCuspidalJacquetMultiplicityProof`

```text
Langlands.glUpperCuspidalJacquetMultiplicityFromFiltration
```

### `Langlands.Representation.Classification.UpperCuspidalJacquetMultiplicityStatement`

```text
Langlands.GLUpperCuspidalJacquetMultiplicityFromFiltrationStatement
```

### `Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionProof`

```text
Langlands.upperJacquetSubrepresentationDetection
```

### `Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionStatement`

```text
Langlands.UpperJacquetSubrepresentationDetectionStatement
```
