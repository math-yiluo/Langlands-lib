# Compact induction from the binary parabolic is the binary product

Author: Worker 837.

Let `a` and `b` be positive ranks and `P` the upper block parabolic of the
binary shape `BlockShape.binary a b ha hb` in `GL_(a+b)(F)`. This pair proves
that compact induction from `P` of any coefficient identified with
`δ_P^(1/2) (A ⊠ B)` on `A ⊗ B` is the published positive-rank binary product
`A × B`, naturally in the pair `(A, B)`. The entry declarations are
`Langlands.PadicField.TopologicalData.binaryPositiveCompactEquivOf` and its
naturality law `binaryPositiveCompactEquivOf_natural`.

The pair is an internal prerequisite of the two `Ψ⁻` clauses
`MirabolicProductMinus.LeftPsiCompatibility` and
`MirabolicProductMinus.RightPsiCompatibility` of
`Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`.
In both clauses, at positive ranks, the localization of the mixed product ends
as compact induction from a binary parabolic. This pair turns that compact
induction into the binary product.

## Provenance

The pair is derived and internal. It states no external theorem. Its results
are compositions of published Library constructions:

- `binaryPairFamilyFunctor` and `binaryPositiveProductFunctor`
  (Induction/BinaryProduct). The positive binary product is the published
  normalized product induction `normalizedProductInductionFunctor` on the
  binary shape (Induction/BlockFactors). Its representation is
  `smoothInduced P (twist (parabolicHalfModulus B) (blockTensor ∘ leviProjection))`.
- `FiniteTensor.binaryLinearEquiv` with `binaryLinearEquiv_external` and
  `binaryLinearEquiv_externalMap`
  (Derivative/MirabolicProductRestrictionFactors): the block tensor of a
  two-factor family is the binary tensor product, and the external action and
  external maps become `TensorProduct.map`.
- `Parabolic.parabolicQuotientCompact` (Parabolic/QuotientCompactProof): the
  coset space `P \ GL_(a+b)(F)` is compact.
- `Induction.compactInclusion_bijective_of_compactSpace`
  (Induction/CompactQuotientProof): for a compact coset space, the inclusion
  of compact induction into smooth induction is bijective.
- `Induction.compactInducedEquiv` (Induction/SplitStagesComparison):
  postcomposition transports compact induction along an equivalence of
  coefficients.
- `twist`, `twistIntertwining`, `Induction.compactInduced`,
  `compactInducedMap`, `compactInclusion`, `eval` and `CompactFunctions`
  (Twist/Definitions, Induction/Definitions).

In BZ77 (Bernstein–Zelevinsky, *Induced representations of reductive p-adic
groups I*, Ann. Sci. ENS (4) 10 (1977), source ID
`bernstein-zelevinsky-1977-induced-i`), the product `ρ_1 × ρ_2` is defined in
§4.1 (printed p.454) as normalized induction `i_{G,M}(ρ_1 ⊗ ρ_2)` from the
standard parabolic. That this is also compact induction follows from the
published compactness of the parabolic coset space. The source's
conventions and their relation to the Library's half modulus are recorded in
`Induction/BinaryProduct.md` and `Induction/BlockFactors.md`. This pair adds no
normalization of its own. The coefficient is exactly the published one.

## Setting

`p` is a prime, `F : PadicField.{uF} p` and `T : F.TopologicalData`. Every
statement uses the topology `T.topology` and the topological group
`T.generalLinearTopologicalGroup (a + b)`. `a` and `b` are natural numbers with
`ha : 0 < a` and `hb : 0 < b`. Write `B = BlockShape.binary a b ha hb` and
`P = B.parabolic F.Carrier`. `X = (A, B)` is a pair of smooth complex
representations of `GL_a(F)` and `GL_b(F)` with carriers in universe `uV`.

## The inducing coefficient

- `binaryPositiveFactors T ha hb X : Fin 2 → Type uV` is the factor family
  `i ↦ (binaryPairFamilyFunctor.obj X i)`, so it is `A` at `0` and `B` at `1`.
- `binaryPositiveTensorEquiv T ha hb X` is the published
  `FiniteTensor.binaryLinearEquiv`, the linear equivalence from the block
  tensor `⨂_i X_i` to `A ⊗ B`.
- `binaryPositiveCoefficient T ha hb X` is the published inducing coefficient
  of the product,

  ```text
  twist (parabolicHalfModulus B) (B.blockTensor (X_i) ∘ B.leviProjection),
  ```

  a representation of `P` on the block tensor.
- `binaryPositiveCoefficient_tensor`: through `binaryPositiveTensorEquiv`, the
  coefficient acts on `A ⊗ B` by

  ```text
  q ↦ δ_P^(1/2)(q) • (A(q₀) ⊗ B(q₁)),
  ```

  where `q₀` and `q₁` are the two diagonal blocks `leviProjection q 0` and
  `leviProjection q 1`, and `δ_P^(1/2)` is `parabolicHalfModulus B`.
- `binaryPositiveCoefficientMap T ha hb f` is the coefficient intertwiner of
  a pair of morphisms `f = (f₁, f₂)`: the twist of the external tensor map of
  `f₁` and `f₂`. `binaryPositiveCoefficientMap_tensor` states that it is
  `f₁ ⊗ f₂` on `A ⊗ B`.

## Compact and smooth induction agree

- `binaryPositiveCompactEquiv T ha hb X` is the representation equivalence

  ```text
  compactInduced P (binaryPositiveCoefficient X)
    ≃ ((binaryPositiveProductFunctor T ha hb).obj X).representation.
  ```

  It is the compact inclusion made into an equivalence by
  `compactInclusion_bijective_of_compactSpace`. The compact-space instance is
  `parabolicQuotientCompact F T B`. The target representation is
  definitionally the published smooth induction of the same coefficient.
- `binaryPositiveCompactEquiv_apply`: the equivalence forgets compact support
  (`rfl`).
- `binaryPositiveCompactEquiv_natural`: for `f : X ⟶ Y`, the equivalence
  carries `compactInducedMap P (binaryPositiveCoefficientMap f)` to the
  published product map `(binaryPositiveProductFunctor T ha hb).map f`
  (`rfl`).

## Arbitrary identified coefficients

Let `W` be a complex vector space in universe `uW` and `κ` a representation
of `P` on `W`. Let `e : W ≃ₗ[ℂ] A ⊗ B` satisfy

```text
he : ∀ q w, e (κ q w) = δ_P^(1/2)(q) • (A(q₀) ⊗ B(q₁)) (e w).
```

- `binaryPositiveCoefficientEquivOf T ha hb X κ e he` is the representation
  equivalence from `κ` to `binaryPositiveCoefficient X`, with linear map
  `binaryPositiveTensorEquiv⁻¹ ∘ e`. The intertwining law is
  `binaryPositiveCoefficient_tensor` together with `he`.
  `binaryPositiveCoefficientEquivOf_apply` states its value (`rfl`).
- `binaryPositiveCompactEquivOf T ha hb X κ e he` is the representation
  equivalence

  ```text
  compactInduced P κ ≃ ((binaryPositiveProductFunctor T ha hb).obj X).representation,
  ```

  the published `compactInducedEquiv` of the previous equivalence followed by
  `binaryPositiveCompactEquiv X`.
- `binaryPositiveCompactEquivOf_eval`: the image of `u` evaluates at
  `x ∈ GL_(a+b)(F)` to `binaryPositiveTensorEquiv⁻¹ (e (u(x)))` (`rfl`).
- `binaryPositiveCompactEquivOf_natural`: let `(κ, e, he)` be data for `X`,
  `(κ', e', he')` data for `Y`, `f : X ⟶ Y`, and `t : κ → κ'` an intertwiner
  with `e' ∘ t = (f₁ ⊗ f₂) ∘ e`. Then the two equivalences carry
  `compactInducedMap P t` to `(binaryPositiveProductFunctor T ha hb).map f`.
  The proof compares values pointwise, through
  `binaryPositiveCoefficientMap_tensor` and the hypothesis on `t`.

The coefficient space `W`, the identification `e` and the intertwiner `t` are
arbitrary. A consumer supplies them from its own localization computation. No
Haar scaling, comparison or invariance premise is added.

## Imports and dependency audit

Direct imports: `Langlands.Representation.Induction.BinaryProduct`,
`Langlands.Representation.Induction.SplitStagesComparison`,
`Langlands.Representation.Induction.CompactQuotientProof`,
`Langlands.Representation.Parabolic.QuotientCompactProof` and
`Langlands.Representation.Derivative.MirabolicProductRestrictionFactors`.

The project import closure has 165 modules besides this one. All of them are
published Library modules (Library commit
`b22e185743f7c318f709e14e422801f4360105d5`):

- `Langlands.Analysis.Local`: ModularCompactAverage, QuotientAutomorphismProof,
  QuotientAutomorphismStatement, QuotientAverageReal, QuotientMass,
  QuotientMeasure, QuotientMeasurePrerequisites, QuotientPositiveLifting,
  QuotientTopology, SplitKernelQuotient.
- `Langlands.Group.GL`: Basic, BlockModulus, Blocks, Maps, Mirabolic,
  MirabolicMixedProductSubgroups, MirabolicModularCharacterProof,
  MirabolicModularCharacterStatement, MirabolicModulusProof,
  MirabolicModulusStatement, MirabolicOppositeIntersection,
  MirabolicProjection, MirabolicRadical, Nonarchimedean,
  NonarchimedeanStatement, NormalizedCharacter, OppositeBlocks, Padic,
  PadicBlocks, PadicOppositeBlocks, RankMaps, RankReindex, ReverseBlocks,
  TriangularParabolic, UpperUnipotent.
- `Langlands.Group`: HaarModulus.
- `Langlands.HarmonicAnalysis`: AlgebraicIntegral, AlgebraicIntegrand, Basic,
  Conductor, PadicAdditiveConductorProof, PadicHaarScalingStatement,
  PadicLatticeTopology, PadicRectangularHaarScalingProof,
  PadicScalarHaarScalingProof.
- `Langlands.LocalFactor.Harmonic`: Statement.
- `Langlands.LocalField`: Canonical, Definitions, Topology.
- `Langlands.LocalField.Normalization`: Definitions, Proof, Statement.
- `Langlands.Representation.Category`: Basic, Twist.
- `Langlands.Representation.Compact`: Definitions, FiniteMean,
  OrbitMeanTranslation, ProjectionProof, ProjectionStatement,
  SurjectivityProof, SurjectivityStatement.
- `Langlands.Representation.Conductor`: Congruence.
- `Langlands.Representation.Derivative`: MinusVanishing, MirabolicCharacter,
  MirabolicLatticeBox, MirabolicMinus, MirabolicProductRestrictionFactors,
  MirabolicProductRestrictionOrbits.
- `Langlands.Representation.Dual`: Definitions.
- `Langlands.Representation.Filtration`: Definitions.
- `Langlands.Representation.Geometric`: ClosedSubgroupDefinitions.
- `Langlands.Representation.Induction`: BinaryProduct, BlockFactors,
  CompactAutomorphism, CompactAutomorphismIntegralProof,
  CompactAutomorphismIntegralStatement, CompactCoinvariantBijectivityProof,
  CompactCoinvariantBijectivityStatement, CompactCoinvariantIntegral,
  CompactCoinvariantLocalInverseProof, CompactCoinvariantLocalInverseStatement,
  CompactLocalSection, CompactLocalSectionSpanningProof,
  CompactLocalSectionSpanningStatement, CompactLocallyConstant,
  CompactQuotientCutoff, CompactQuotientProof, CompactSurjectivityProof,
  CompactSurjectivityStatement, CompactTransitivityProof,
  CompactTransitivityStatement, Definitions, InverseTranspose,
  NormalCoinvariantKernelProof, NormalCoinvariantKernelStatement,
  NormalCoinvariantMap, NormalCoinvariantProof, NormalCoinvariantStatement,
  NormalSplitComparison, OppositeParabolic, Parabolic, SplitKernelCompact,
  SplitKernelCovariance, SplitKernelEquivariant, SplitKernelIntegral,
  SplitQuotientProof, SplitQuotientStatement, SplitStagesComparison,
  SplitStagesRetraction, StructuralStatement, SurjectivityProof,
  SurjectivityStatement.
- `Langlands.Representation.Jacquet`: CharacterAveraging, Coinvariants,
  Localization, PositiveCharacter, SmoothTwist.
- `Langlands.Representation.MatrixCoefficient`: Definitions, LawsProof,
  LawsStatement.
- `Langlands.Representation.Mirabolic`: MixedProducts.
- `Langlands.Representation.Parabolic`: GeometricPrerequisitesStatement,
  QuotientCompactProof.
- `Langlands.Representation.RankinSelberg`: GeneralLinearUnimodularity,
  LastRowCompactOrbitProof, LastRowCompactOrbitStatement, Measures,
  QuotientIntegrals, UnimodularityStatement, ZeroRowLastRowCutoffProof,
  ZeroRowLastRowCutoffStatement.
- `Langlands.Representation.Smooth.Admissibility`: CofinalProof,
  CofinalStatement.
- `Langlands.Representation.Smooth`: Definitions.
- `Langlands.Representation.Smooth.SmoothPart`: BasicProof, BasicStatement,
  Definitions.
- `Langlands.Representation.Smooth.Transfer`: PullbackProof, PullbackStatement,
  SubquotientProof, SubquotientStatement.
- `Langlands.Representation.Tensor`: Finite, FiniteEquivalences, OneFactor.
- `Langlands.Representation.Twist`: AdmissibilityProof, AdmissibilityStatement,
  AlgebraProof, AlgebraStatement, ContinuousCharacterProof,
  ContinuousCharacterStatement, Definitions, RealPower, SmoothProof,
  SmoothStatement, SubquotientDefinitions, SubquotientProof,
  SubquotientStatement.
- `Langlands.Representation.Whittaker`: Algebraic, GeneralLinear, Iwasawa.
- `Langlands.Topology`: CompactNormCharacter.
- `Langlands.Topology.CompactOpen`: ConjugationStabilizer, NeighborhoodBasis,
  NeighborhoodBasisStatement.
- `Langlands.Topology.Nonarchimedean`: Subgroup.

Notes on the closure:

- `Derivative/MirabolicProductRestrictionFactors` and
  `Derivative/MirabolicProductRestrictionOrbits` are published helper modules
  of the mirabolic restriction sequence. Only the three
  `FiniteTensor.binaryLinearEquiv` declarations named above are used. No
  restriction-sequence conclusion is used.
- `Derivative/MinusVanishing` enters only through the import of
  `MirabolicProductRestrictionOrbits`. Nothing from it is used.
- `Whittaker/Iwasawa` enters through `Parabolic/QuotientCompactProof`, whose
  compactness proof uses the Iwasawa decomposition. `Whittaker/Algebraic` and
  `Whittaker/GeneralLinear` contain only Whittaker character and
  coefficient-model definitions. `Filtration/Definitions` contains only
  definitions.

No module in the closure is a plus functor or adjunction module, §4.13(d), a
Leibniz or filtration proof, a finiteness or classification consumer, a
supercuspidal or segment conclusion, or a Whittaker finiteness statement. No
clause of `MirabolicProductMinusCompatibilityStatement` is imported or used.
The proofs use only the published theorems named above and Mathlib. No
proposition definition is used as a hypothesis. Axioms: `propext`,
`Classical.choice` and `Quot.sound`. Universe parameters are `uF`, `uV`, `uW`
and `uW'`, independent.
