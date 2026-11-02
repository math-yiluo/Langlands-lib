# Support bound for derivatives of supplied special heads: proof

Authors: Worker 890 (this module and the six helper modules
`SegmentHeadSupport{Generic,LeftExact,Leibniz,Cons,Split,Step}`) and
Worker 256 (the base-case module `SegmentHeadDerivativeSupportLengthTwo`).

## Target

`Langlands.Classification.segmentHeadDerivativeSupportTruncation` has outer
parameters `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)` and type exactly

```text
SegmentHeadDerivativeSupportTruncation.{uF, uV} F T
```

from the unchanged published module
`Langlands.Representation.Classification.SegmentHeadDerivativeSupportTruncationStatement`.
After `letI := T.topology`, the proposition quantifies over every
continuous nontrivial unitary additive character `ψ`, every segment
`Δ : T.Segment.{uV,uF}`, every
`π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)` with
`T.IsSegmentHead Δ π`, every `k ≤ Δ.degree` (including `0` and
`Δ.degree`), and every irreducible actual subquotient `σ` of the order-`k`
general-linear derivative of `π`. It asks for an actual multiset `s` of
cuspidal data in universe `uV` and an optional segment `A` with
`T.IsSupercuspidalSupport σ s`, `Segment.IsTerminalTruncation A Δ` and
`{ρ | ρ ∈ s} = Segment.optionalSupport A`. For `A = some E` the terminal
relation means `E.support ⊆ Δ.support` and `Δ.last ∈ E.support`; `none` has
empty support.

The theorem adds no premise. Its universe parameters are exactly `uF` and
`uV`, and they stay independent. The proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Proof

The theorem is the term

```text
SegmentHeadSupport.supportTruncation_of_base T
  (fun Δ hΔ ψ π hπ k hk σ hσ hsub =>
    SegmentHeadDerivativeSupportLengthTwo.lengthOne_support F T ψ Δ hΔ π hπ k hk σ hσ hsub)
  (fun Δ hΔ ψ π hπ k hk σ hσ hsub =>
    SegmentHeadDerivativeSupportLengthTwo.lengthTwo_support F T ψ Δ hΔ π hπ k hk σ hσ hsub)
```

Write `Δ = [ρ, ν^(m-1) ρ]` with `m = Δ.length` and `ν = |det|`.

1. **Length one and two** (Worker 256, module
   `SegmentHeadDerivativeSupportLengthTwo`). `lengthOne_support` and
   `lengthTwo_support` prove the conclusion for every `Δ` of length one and
   of length two. Order `0` gives the cuspidal content of `Δ` and order
   `deg Δ` the empty support. For length one the head is supercuspidal, and
   its intermediate derivatives vanish (BZ77 §4.4). For length two,
   `Δ = [ρ, νρ]` with `r = rank ρ`, the Leibniz filtration of `ρ × νρ` leaves
   only the order `r`. There the kernel `K` of `ρ × νρ ↠ π` is nonzero, by
   the reducibility of `ρ × νρ`, and BZ77 Lemma 4.7(b) with integral
   twist-freeness shows that `νρ` does not embed into `K^(r)`. A lattice
   argument on the two-step filtration of `(ρ × νρ)^(r)`, whose factors are
   `ρ` and `νρ`, then makes the order-`r` derivative of
   `π` is a quotient of `νρ`, with support `{νρ}`, the support of the
   terminal truncation `[νρ]`. The reducibility of `ρ × νρ` is the only use
   of the two-supercuspidal result, as permitted by the operator response
   cited below. The module's Markdown describes its proof and audits its
   closure.
2. **The inductive step** (module `SegmentHeadSupportStep`). For
   `m = k + 2 ≥ 3`, assume the conclusion for all segments of length
   `k + 1`. Two published individual-head constructions place a head `π` of
   `Δ` in two products:
   - `π` is a subrepresentation of `ν^(k+1) ρ × π'`, where `π'` is a head of
     `[ρ, ν^k ρ]`. Indeed `ν^(k+1) ρ × π'` embeds into the decreasing
     induction of `Δ`, whose irreducible subrepresentations are all
     equivalent to `π` (`SegmentHeadDecreasingSocle`).
   - `π` is a quotient of `ρ × π''`, where `π''` is a head of
     `[νρ, ν^(k+1) ρ]`. Indeed the increasing induction of `Δ` maps onto
     `ρ × π''`, and every irreducible quotient of it is equivalent to its
     head `π`.

   The Leibniz filtration (BZ77 Corollary 4.14(c)) and the derivatives of
   supercuspidal representations (BZ77 §4.4) show that every irreducible
   subquotient of a derivative of `ρ₀ × π'` lies in `ρ₀ × τ` for an
   irreducible subquotient `τ` of a derivative of `π'`, or in a derivative of
   `π'` itself. With the induction hypothesis, the first product gives a
   support of `σ` whose set is a terminal window of `[ρ, ν^k ρ]`, possibly
   with `ν^(k+1) ρ` added. The second gives a support whose set is a terminal
   window of `[νρ, ν^(k+1) ρ]`, possibly with `ρ` added. Uniqueness of
   supercuspidal supports identifies the two supports when they are nonzero.
   Integral twist-freeness (`ν^a ρ = ρ` only for `a = 0`) leaves only the
   terminal windows of `Δ`, which are exactly the optional supports of the
   terminal truncations of `Δ` (`exists_terminal_iff`).
3. **Assembly.** `headSupportBound_of_base` inducts on the length, and
   `supportTruncation_of_base` restates the result as the target proposition.

The paired Markdown of each helper module describes its declarations and
proofs in detail:

| Module, prefixed by `Langlands.Representation.Classification.` | Content |
| --- | --- |
| `SegmentHeadSupportGeneric` | Laws of actual subquotients, the short-exact splitting of irreducible subquotients, and the composition-series lemma `exists_irreducible_of_isSubquotient_map` for exact functors |
| `SegmentHeadSupportLeftExact` | Exactness of `X ↦ L × X` for the binary normalized product |
| `SegmentHeadSupportLeibniz` | The two Leibniz cases for a derivative of `L × X` with supercuspidal `L` |
| `SegmentHeadSupportCons` | Supports of irreducible subquotients of `ρ₀ × τ`, and rank-cast transport |
| `SegmentHeadSupportSplit` | First-factor splittings of the increasing and decreasing segment inductions, and twisted representatives |
| `SegmentHeadSupportStep` | Windows and terminal truncations, the two sides, the inductive step and the assembly lemmas |
| `SegmentHeadDerivativeSupportLengthTwo` | The cases of length one and two (Worker 256) |

## Scope

The theorem is exactly support-only. It gives no multiplicity formula, no
relation between the truncation length and the derivative order, no count
of simple factors, no identification of a derivative with a truncated head,
and no irreducibility or nonvanishing of a derivative. It proves neither
direction of the full `SegmentHeadProductIrreducibility` criterion.

## Sources and provenance

The statement is an internal support-only weakening motivated by
Zelevinsky 1980, §9.8, printed p.199 (one-based PDF page 36), where
Proposition 9.6 is rewritten as `⟨Δ⟩^t(derivatives) = Σ_{Δ' ←| Δ} ⟨Δ'⟩^t`
over the empty set and the subsegments `Δ'` of `Δ` containing its end.
Registered source `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`. The
proof does not follow the printed argument. It uses neither Proposition
9.6 (printed p.198), nor Theorem 3.5, nor any of their proofs or proof
successors. No applicable errata entry for this source is registered in
the project literature index or the public notes.

The derivative theory used is general Bernstein–Zelevinsky 1977
(`bernstein-zelevinsky-1977-induced-i`): exactness of the derivatives
(Proposition 3.2 and §3.5), derivatives of supercuspidal representations
(§4.4, Gelfand–Kazhdan), the Leibniz filtration (Corollary 4.14(c)) and
finite length of derivatives (the published internal theorem
`generalLinearDerivativeFiniteLength`). Every one of these enters through
an independently accepted and published Lean proof.

## Operator authorization

- [30144f6f9b59540b88b6d4c1517892d9](/home/taskhub/pilot/correspondence/30144f6f9b59540b88b6d4c1517892d9.md)
  (request `7bd9e666c60d53469eff04b2962e1acf`) authorizes a new proof of
  exactly this support-only statement from independently published general
  derivative theory and the permitted individual-head constructions.
- [bd71b9185aab5d6eafffb7891bd3a3ca](/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md)
  allows a fully proved general BZ77 derivative route.
- [0edda6122ce65ed7ac51603c37473920](/home/taskhub/pilot/correspondence/0edda6122ce65ed7ac51603c37473920.md)
  fixes what counts as general derivative theory and general infrastructure:
  the Ze80 3.7(b) comparison through the Lemma 4.7(b) closure, Ze80 5.3
  `leftMixedProductHomogeneity` and the nine generic modules.
- [09565d9017ef55faa68ad9890c242aed](/home/taskhub/pilot/correspondence/09565d9017ef55faa68ad9890c242aed.md)
  (given for task `451717b1`) admits `cuspidalProductMirabolicSupportShift`
  (BZ77 Lemma 4.7(b)) with its whole closure, including the Ze80 3.7(b)
  comparison, as general derivative theory; `0edda612` applies this to the
  present task.
- [2b33898bdd0a5ff1b9031be5155a06f0](/home/taskhub/pilot/correspondence/2b33898bdd0a5ff1b9031be5155a06f0.md)
  (to Worker 256, request `64f1e681367a5c0d9de435c691ff88dc`) and the
  identical
  [ca18fd5005bf5e12a3f7cade18dca865](/home/taskhub/pilot/correspondence/ca18fd5005bf5e12a3f7cade18dca865.md)
  (to Worker 890, request `ed8a8370090a54889b93b78b2fa95abc`) permit importing
  `twoSupercuspidalAdjacentProductReducible` (proof task `0988a3e0`) with its
  published closure, solely for the reducibility of `ρ × νρ`, and nothing
  else from Ze80 1.11. The target implies this reducibility, so no proof can
  avoid it.

These permissions are not mathematical proofs; every input is a published
Lean theorem.

## Direct imports

| Direct import, prefixed by `Langlands.Representation.Classification.` | Project closure, including that import | Role |
| --- | ---: | --- |
| `SegmentHeadSupportStep` | 1065 | `supportTruncation_of_base`: the inductive step and the assembly |
| `SegmentHeadDerivativeSupportLengthTwo` | 1164 | `lengthOne_support` and `lengthTwo_support` |

The six helper modules import the following published modules besides each
other and Mathlib. The role of each is described in the helper Markdown.

| Published import of a helper module, prefixed by `Langlands.Representation.` | Project closure, including that import |
| --- | ---: |
| `Tensor.SmoothSubquotients` | 148 |
| `Exponents.WeylBranchPiecesSubquotient` | 126 |
| `Induction.BinaryProduct` | 36 |
| `Parabolic.InductionExactnessProof` | 53 |
| `Shahidi.IntertwiningInduced` | 96 |
| `Filtration.LengthCriterionProof` | 4 |
| `Derivative.GeneralLinearDerivativeLeibnizFiltrationProof` | 324 |
| `Classification.SupercuspidalDerivativesProof` | 304 |
| `Classification.SupercuspidalSupport` | 58 |
| `Parabolic.HeadTailProductInduction` | 152 |
| `Induction.SingleBlock` | 32 |
| `Classification.SegmentHeadDecreasingSocle` | 653 |
| `Classification.SupercuspidalSupportUniquenessProof` | 431 |
| `Classification.CuspidalIntegralTwistFreenessProof` | 55 |
| `Classification.IrreducibleProductFiniteLengthProof` | 477 |
| `Classification.SegmentTruncationObstructionStatement` | 51 |
| `Classification.SegmentHeadDerivativeSupportTruncationStatement` | 81 |
| `Derivative.GeneralLinearDerivativeFiniteLengthProof` | 860 |
| `Derivative.ProductVanishing` | 85 |
| `Category.FiniteIndexRestriction` | 2 |

The base-case module `SegmentHeadDerivativeSupportLengthTwo` has the
following direct imports; its Markdown records their roles:

- `Classification.SegmentTruncationObstructionStatement`
- `Induction.BinaryProduct`
- `Induction.SingleBlock`
- `Derivative.GeneralLinearDerivativeLeibnizFiltrationProof`
- `Derivative.GeneralLinearDerivativeExactnessProof`
- `Derivative.RestrictionBridge`
- `Classification.SupercuspidalDerivativesProof`
- `Classification.CuspidalProductMirabolicSupportShiftProof`
- `Classification.SegmentHeadTopDerivative`
- `Classification.CuspidalIntegralTwistFreenessProof`
- `CuspidalSupport.JacquetVanishingHelpers`
- `Exponents.WeylBranchPiecesSubquotient`
- `Tensor.SmoothSubquotients`
- `Filtration.ZeroFactorDeletionProof`
- `Filtration.SubsingletonProof`
- `Filtration.FunctorLengthTwoDetection`
- `Classification.SegmentCuspidalContent`
- `Derivative.OrderedCuspidalProductHeadShift`
- `Classification.TwoSupercuspidalAdjacentReducibilityProof`

Closure sizes overlap and are not additive.

## Complete import closure

A recursive inventory follows the project imports of this module, stopping at
external Mathlib and Lean roots. The closure has 1199 project modules,
including this root, and 317 distinct external import roots. Eight
modules are new in this candidate: this module, the six helper modules and
`SegmentHeadDerivativeSupportLengthTwo`. The other 1191 modules are
published Library pairs. Their Lean and Markdown files are byte-identical to
Library commit `7a2e42fd31831029d34cafb155ffad911920df25` (0
differences), and no module of the closure lacks its paired Markdown
(0 missing). The base-case Markdown records its audit at the
earlier commit `df7769b33f1b2e786f8bb0ac3ff1a6fd8a49020e` and rechecks it at
`7a2e42fd31831029d34cafb155ffad911920df25`. Between the two
commits the Library only added modules outside this closure and changed one
unrelated Markdown file, so no file of the closure differs. The complete
listing and the external roots are in the appendices.

The closure is the union of two parts.

- **The helper part.** The closure of `SegmentHeadSupportStep` has
  1065 modules. Apart from the six helper modules, all but
  41 of them lie in the 1095-module closure of the
  published `Classification.SegmentHeadTopDerivative`. That module was
  published for the same host with the same Independence boundary, and its
  Markdown audits that closure in full. The 41 further
  modules are: `Langlands.Group.GL.NestedRefinement`, `Langlands.HarmonicAnalysis.SmoothWeakIntegral`, `Classification.NormalizedProductFiniteLengthProof`, `Classification.RelativeGenericityStatement`, `Classification.RelativeJacquetMultiplicityStatement`, `Classification.RelativeRegularComparisonStatement`, `Classification.SegmentHeadDerivativeSupportTruncationStatement`, `Classification.SegmentTruncationObstructionStatement`, `CuspidalSupport.IrreducibleLeviAdmissibilityProof`, `CuspidalSupport.IrreducibleLeviAdmissibilityStatement`, `CuspidalSupport.MinimalRefinedJacquetProof`, `CuspidalSupport.MinimalRefinedJacquetStatement`, `CuspidalSupport.RefinedQuasicuspidalEmbeddingProof`, `CuspidalSupport.RefinedQuasicuspidalEmbeddingStatement`, `Derivative.DerivativeEquivTransport`, `Derivative.GeneralLinearDerivativeFiniteLengthProof`, `Derivative.GeneralLinearDerivativeFiniteLengthStatement`, `Derivative.ProductDerivativesFiniteLength`, `Exponents.ComplexTwistFamilies`, `Exponents.RealTwistFamilies`, `Exponents.SupportedRegularMultiplicityBranchObstructionStatement`, `Exponents.WeylBranchPiecesStatement`, `Exponents.WeylBranchPiecesSubquotient`, `Filtration.FactorMatchingPullback`, `Filtration.JordanHolderProof`, `Parabolic.ExactnessReciprocityStatement`, `Parabolic.InductionExactnessProof`, `Shahidi.IntertwiningCovariance`, `Shahidi.IntertwiningInduced`, `Shahidi.IntertwiningIntegral`, `Smooth.Admissibility.ExactProof`, `Smooth.Admissibility.ExactStatement`, `Smooth.Admissibility.FiniteLengthProof`, `Smooth.Admissibility.FiniteLengthStatement`, `Smooth.FiniteLengthGrothendieck`, `Tensor.ExternalSubquotient`, `Tensor.FactorMatchingProof`, `Tensor.FactorMatchingStatement`, `Tensor.SmoothSubquotients`, `Twist.LeviComplexPower`, `Twist.LeviRealPower`. They are accounted for below.
- **The base-case part.** The closure of
  `SegmentHeadDerivativeSupportLengthTwo` has 1164 modules, and
  133 of them lie outside the helper part:
  - the base-case module itself;
  - 77 modules of the audited closure of
    `SegmentHeadTopDerivative`, which the base-case module imports directly;
  - 2 further published modules, `Classification.SegmentCuspidalContent` and `Filtration.FunctorLengthTwoDetection`.
    `SegmentCuspidalContent` defines the multiset of members of a segment
    and proves elementary membership and cardinality lemmas.
    `FunctorLengthTwoDetection` is a lattice-theoretic helper with no p-adic
    input. It was published for the proof of Zelevinsky 1980, Proposition
    4.6, but contains no conclusion of that proposition. The base-case module
    uses only `FunctorLengthTwo.subtypeMap` from it;
  - 53 modules reached only through the authorized import
    `TwoSupercuspidalAdjacentReducibilityProof` (marked `*` below). These are
    the reducibility proof and its statement, its unitarity and
    non-unitarizability inputs, the Ze80 1.11(a) nonadjacent irreducibility
    proof with its helpers, and general unitary and integral-form
    infrastructure. Responses `2b33898b`/`ca18fd50` cover them as part of the
    published closure of that theorem.

  The Markdown of `SegmentHeadDerivativeSupportLengthTwo` audits each of
  these modules. The list:

- `Langlands.Group.GL.BlockScalarCenter` *
- `Langlands.Group.GL.CentralQuotientTopologyProof` *
- `Langlands.Group.GL.CentralQuotientTopologyStatement` *
- `Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof` *
- `Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement` *
- `Langlands.HarmonicAnalysis.RowSchwartzAction`
- `Langlands.HarmonicAnalysis.RowTestSmoothProof`
- `Langlands.HarmonicAnalysis.RowTestSmoothStatement`
- `Langlands.LocalField.SmoothCharacterNormProof` *
- `Langlands.LocalField.SmoothCharacterNormStatement` *
- `Classification.ConstituentCompatibility` *
- `Classification.CuspidalProductContragredient`
- `Classification.CuspidalProductDerivativeQuotientSupport`
- `Classification.CuspidalProductMirabolicSupportShiftProof`
- `Classification.CuspidalProductMirabolicSupportShiftStatement`
- `Classification.ExponentFamily` *
- `Classification.IrreducibleTwoFactorProductSwapProof` *
- `Classification.IrreducibleTwoFactorProductSwapStatement` *
- `Classification.LanglandsData`
- `Classification.MirabolicDerivativeContragredient`
- `Classification.NonadjacentAssembly` *
- `Classification.NonadjacentLeibnizPieces` *
- `Classification.NonadjacentSpecialization` *
- `Classification.NonadjacentTwoBlock` *
- `Classification.SegmentCuspidalContent`
- `Classification.SegmentDecreasingCuspidalProduct`
- `Classification.SegmentHeadDerivativeSupportLengthTwo`
- `Classification.SegmentHeadProductFiniteness`
- `Classification.SegmentHeadTopDerivative`
- `Classification.SupercuspidalContragredient`
- `Classification.SupercuspidalContragredientProof`
- `Classification.TwistedProductCharacterTwistProof` *
- `Classification.TwoBlockExponentNonUnitarizabilityProof` *
- `Classification.TwoBlockExponentNonUnitarizabilityStatement` *
- `Classification.TwoSupercuspidalAdjacentReducibilityProof` *
- `Classification.TwoSupercuspidalAdjacentReducibilityStatement` *
- `Classification.TwoSupercuspidalBinaryProductBridge` *
- `Classification.TwoSupercuspidalDerivativeBridge` *
- `Classification.TwoSupercuspidalNonadjacentIrreducibilityProof` *
- `Classification.TwoSupercuspidalProductDualTwist` *
- `Classification.TwoSupercuspidalProductStructureStatement` *
- `Classification.UnitaryGenericCompatibilityStatement` *
- `CuspidalSupport.WholeLeviTransport`
- `Derivative.LeftMixedProductHomogeneityProof`
- `Derivative.LeftMixedProductHomogeneityStatement`
- `Derivative.LeftMixedProductPhiHatIterate`
- `Derivative.MirabolicDerivativeUnitInjective`
- `Derivative.MirabolicHighestDerivativeDescent`
- `Derivative.MirabolicHighestDerivativePairingProof`
- `Derivative.MirabolicHighestDerivativePairingStatement`
- `Derivative.MirabolicMinusNormalization`
- `Derivative.MirabolicMinusPairingTransferProof`
- `Derivative.MirabolicMinusPairingTransferStatement`
- `Derivative.MirabolicPhiMinusNondegeneratePairing`
- `Derivative.MirabolicPlusNormalization`
- `Derivative.MirabolicProductMinusCompatibility`
- `Derivative.MirabolicSmoothPhiPlus`
- `Derivative.MirabolicSmoothPhiPlusAdjunction`
- `Derivative.MirabolicSmoothPhiPlusIterate`
- `Derivative.MirabolicSmoothPhiPlusProduct`
- `Derivative.OrderedCuspidalProductHeadShift`
- `Derivative.OrderedCuspidalProductNondegeneracyProof`
- `Derivative.OrderedCuspidalProductNondegeneracyStatement`
- `Derivative.OrderedCuspidalProductTwistOne`
- `Derivative.Partial`
- `Derivative.PartialDerivativeJacquetComparisonProof`
- `Derivative.PartialDerivativeJacquetComparisonStatement`
- `Derivative.PartialDerivativeJacquetLHS`
- `Derivative.PartialDerivativeJacquetNormalization`
- `Derivative.PartialDerivativeJacquetRHS`
- `Derivative.PartialDerivativeJacquetRHSComparison`
- `Derivative.PartialLocalizationCharacter`
- `Derivative.PartialLocalizationData`
- `Derivative.RestrictedProductLevel`
- `Derivative.RestrictionBridge`
- `Derivative.RightMixedLevel`
- `Derivative.RightMixedProductPhiMinusDetectionProof`
- `Derivative.TopLine`
- `Derivative.TopLocalizationData`
- `Filtration.FunctorLengthTwoDetection`
- `Filtration.InvariantBilinear`
- `Filtration.InvariantBilinearBounds`
- `Filtration.InvariantBilinearSubquotientBounds` *
- `Filtration.SmoothDualEvaluation` *
- `Induction.BlockCharacterAbsorption`
- `Induction.CompactIntegralForm` *
- `Induction.CovariantRescaling` *
- `Induction.NormalizedIntegralForm` *
- `Jacquet.LocalizationTower`
- `MatrixCoefficient.HermitianProduct` *
- `MatrixCoefficient.NormRegularityProof` *
- `MatrixCoefficient.NormRegularityStatement` *
- `Parabolic.InverseTransposeProductProof` *
- `Parabolic.InverseTransposeProductStatement` *
- `Parabolic.NormalizedCompatibilityStatement` *
- `RankinSelberg.EqualRankFrobeniusProof`
- `RankinSelberg.EqualRankFrobeniusStatement`
- `RankinSelberg.EqualRankTrilinearAssembly`
- `RankinSelberg.EqualRankTrilinearReduction`
- `RankinSelberg.EqualRankTrilinearUniquenessStatement`
- `RankinSelberg.LocalFactor`
- `RankinSelberg.RankOneQuotient`
- `RankinSelberg.TwistInvariance`
- `RankinSelberg.UnipotentQuotient`
- `Tensor.FlattenedGLRefinement`
- `Tensor.SmoothDual`
- `Tensor.SmoothDualInjectivityProof`
- `Tensor.SmoothDualInjectivityStatement`
- `Tensor.SmoothDualSurjectivityProof`
- `Tensor.SmoothDualSurjectivityStatement`
- `Tensor.UnitaryProof` *
- `Tensor.UnitaryStatement` *
- `Twist.PullbackProof` *
- `Twist.PullbackStatement` *
- `Unitary.CentralCharacterProof` *
- `Unitary.CentralCharacterStatement` *
- `Unitary.HermitianDual` *
- `Unitary.LeviCuspidalRealUnitarizationProof` *
- `Unitary.LeviCuspidalRealUnitarizationStatement` *
- `Unitary.SquareIntegrableProof` *
- `Unitary.SquareIntegrableStatement` *
- `Unitary.SupercuspidalRealUnitarizationProof` *
- `Unitary.SupercuspidalRealUnitarizationStatement` *
- `Unitary.Twist` *
- `Unitary.UnitarizabilityContinuationProof` *
- `Unitary.UnitarizabilityContinuationStatement` *
- `Whittaker.AlgebraicTwist`
- `Whittaker.CharacterChange`
- `Whittaker.EntrywiseCharacter`
- `Whittaker.MirabolicQuotientMeasure`
- `Whittaker.PrerequisiteInterfaces`
- `Whittaker.PrerequisitesStatement`
- `Whittaker.Twist`

## The modules beyond the earlier audited closure

The helper part adds the following published modules to the audited closure
of `SegmentHeadTopDerivative`.

- 21 modules enter only through
  `Derivative.GeneralLinearDerivativeFiniteLengthProof`: that proof, its
  statement, the helpers `DerivativeEquivTransport` and
  `ProductDerivativesFiniteLength`, and their finite-length, Jordan–Hölder,
  admissibility and factor-matching infrastructure
  (`Smooth.Admissibility.*`, `Filtration.JordanHolderProof`,
  `Filtration.FactorMatchingPullback`, `Tensor.FactorMatching*`,
  `Smooth.FiniteLengthGrothendieck`, `CuspidalSupport.IrreducibleLeviAdmissibility*`,
  `CuspidalSupport.MinimalRefinedJacquet*`,
  `CuspidalSupport.RefinedQuasicuspidalEmbedding*`,
  `Classification.NormalizedProductFiniteLengthProof`,
  `Group.GL.NestedRefinement`). The published Markdown of
  `GeneralLinearDerivativeFiniteLengthProof` audits its whole closure
  against the same exclusion list as this host. Its route is general BZ77:
  exactness of derivatives, the embedding of an irreducible representation
  into a product of supercuspidal representations (BZ77 §4.1), and finite
  length of derivatives of such products through the Leibniz filtration and
  §4.4. It uses no theorem of Zelevinsky 1980.
- 12 modules enter through `Tensor.SmoothSubquotients` and
  `Exponents.WeylBranchPiecesSubquotient`, which supply the bridge between
  actual smooth subquotients and representation-level subquotients and the
  lemma `WeylBranchPieces.IsGluedFrom.exists_isSubquotient_piece`. Besides
  these two modules and `Tensor.ExternalSubquotient` (linear algebra of
  external tensors), they are definition units (`Exponents.RealTwistFamilies`,
  `Exponents.ComplexTwistFamilies`, `Twist.LeviRealPower`,
  `Twist.LeviComplexPower`) and Prop-valued statement modules
  (`Exponents.WeylBranchPiecesStatement`,
  `Exponents.SupportedRegularMultiplicityBranchObstructionStatement`,
  `Classification.RelativeGenericityStatement`,
  `Classification.RelativeJacquetMultiplicityStatement`,
  `Classification.RelativeRegularComparisonStatement`). The statement
  modules define propositions and prove none; no proof uses them.
- `Parabolic.InductionExactnessProof` and its statement
  `Parabolic.ExactnessReciprocityStatement`, imported directly and also
  through the finite-length proof: exactness of normalized parabolic
  induction (BZ77 Proposition 1.9(a)).
- `Shahidi.IntertwiningInduced`, `Shahidi.IntertwiningCovariance`,
  `Shahidi.IntertwiningIntegral` and `HarmonicAnalysis.SmoothWeakIntegral`:
  the helper modules use only the tensor splitting `Shahidi.pairSplit` and
  `Shahidi.pairSplit_tprod` from them. No intertwining operator or integral
  enters a proof here.
- `Classification.SegmentTruncationObstructionStatement`: definitions of
  terminal truncation and optional support, imported by the target statement
  itself. Its proposition definition is not used.
- `Classification.SegmentHeadDerivativeSupportTruncationStatement`: the
  target statement.

## Mathematical dependency audit

The proof uses the following published theorems. Their implemented routes
were checked in their paired Markdown, in addition to the name scan below.

1. **Individual-head constructions.** `segmentSpecialConstituentExistence`,
   `IsSegmentHead.decreasingSocleEmbedding`,
   `IsSegmentHead.nonempty_equiv_of_down_subrepresentation` and
   `isSegmentHead_iff`. These are the already permitted independent
   individual-head constructions. The existence proof constructs a common
   image of a nonzero map from increasing to decreasing induction; actual
   geometric-lemma filtrations and cuspidal Jacquet multiplicity force that
   image to be irreducible with the strong head and socle properties. The
   multiplicity input `SegmentJacquetMultiplicity*` is multiplicity one of
   the segment tensor in the Jacquet module of a segment induction, a
   geometric-lemma count. It is not one of the excluded segment Jacquet
   formulas. None of these constructions uses a derivative formula or the
   product criterion.
2. **Supercuspidal supports.** `glSupercuspidalSupportUniqueness`
   (Zelevinsky 1980, Proposition 1.10) is proved through the reverse
   association of BZ77 Theorem 2.9(a); its closure contains no derivative
   module. `cuspidalIntegralTwistFreeness` is proved with the central
   character of an admissible irreducible representation.
3. **Finite length and nonvanishing of products.**
   `irreducibleProductFiniteLength` embeds an irreducible product into a
   cuspidal induction of finite length. `ProductVanishing.nontrivial_binary`
   shows that a binary product of nonzero representations is nonzero.
4. **General derivative theory (BZ77).** `generalLinearDerivativeExactness`,
   `generalLinearDerivativeLeibnizFiltration` (Corollary 4.14(c)),
   `supercuspidalDerivatives` (§4.4, Gelfand–Kazhdan) and
   `generalLinearDerivativeFiniteLength`.
5. **General induction.** `Parabolic.normalizedInductionExactness`,
   `headTailProductInductionIso`, `singleBlockNormalizedProductEquiv`, the
   binary product functors with their unit laws, and
   `FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom`.
6. **The base cases.** `lengthOne_support` and `lengthTwo_support` of
   `SegmentHeadDerivativeSupportLengthTwo`, whose Markdown records their
   proof, the published declarations they use and their closure. Besides
   the general derivative theory of item 4 and the twist-freeness of item 2,
   they use `segmentHeadTopDerivativeNontrivial` (BZ77 4.11 with the
   individual decreasing-socle embedding),
   `cuspidalProductMirabolicSupportShift` (BZ77 Lemma 4.7(b), admitted with
   its closure by `09565d90` and `0edda612`) and
   `OrderedCuspidalProductHeadShift.irreducible_support_of_injective`. The
   length-two case uses the published
   `twoSupercuspidalAdjacentProductReducible` only for the reducibility of
   `ρ × νρ`, as permitted by the responses `2b33898b` and `ca18fd50`.

Several short generic lemmas of the helper modules repeat constructions
found in Library modules that are not imported (rank-zero product helpers,
`twistIsoOfEq`, two shape equations of `SegmentProductSplit`, and the
irreducible-quotient argument). Each is proved in full in the helper
modules from published definitions; no excluded conclusion is involved.

## Exclusions

A comment- and string-stripped scan of the Lean sources of the whole closure
for the names of the excluded conclusions (`GenericSegmentProductUniqueness`,
`SegmentHeadProductIrreducibility`, `SquareIntegrableLanglandsClassification`,
`SegmentFullJacquet`, `SegmentHeadJacquet`, `SegmentSocleJacquet`,
`SegmentSpecialJacquetExponentNorm`, `SegmentSocleDerivative`,
`SegmentSocleProduct`, `AdjacentQuotientUpperProduct`, `LinkedSegment`,
`SegmentSpecialEssential`, `CoinvariantFinite`, `QuotientCoverage`,
`StrongHeadExist`, `TemperedUniqueness`, `Aubert`) finds none of them. The
names `TwoSupercuspidal`, `NonadjacentLeibniz` and
`TwoSupercuspidalProductStructure` occur only in the base-case module and in
modules reached only through the authorized reducibility import. Outside its
own statement module, `TwoSupercuspidalProductStructure` occurs only in
imports of the statement module `TwoSupercuspidalProductStructureStatement`,
which proves nothing. `TwoSupercuspidalProductStructureProof` is not in the
closure. The word `Exhaust` occurs only in generic section and definition names
(`CompactCoefficient.AdmissibleComplement`, `Jacquet.CharacterAveraging`,
`Parabolic.GeometricPrerequisitesStatement`). These concern the isotypic
decomposition of an admissible representation and exhaustions of a unipotent
radical by compact open subgroups. None is an excluded exhaustion theorem.
The proof routes above preserve the following exclusions, including proof
successors, renamings and transitive uses.

| Excluded conclusion | Dependency check |
| --- | --- |
| Parent `GenericSegmentProductUniqueness`, task `30341ae4-65f2-4a0e-9283-763db01a409e` | No import or proof use |
| Multisegment exhaustion, task `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` | No import or proof use |
| Ordered strong-head existence, task `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | No import or proof use; the individual-segment existence proof is a different result |
| Quotient coverage, task `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` | No import or proof use |
| Ordered conversion, task `8252833d-c269-41a9-824c-5879e531b23b` | No import or proof use |
| Tempered uniqueness, task `52e97845-36bb-457d-b76f-70753334b88c` | No import or proof use; `Classification.Tempered`, `TemperedInductionStatement` and `TemperedSupportStatement` (in the audited `SegmentHeadTopDerivative` closure) contain only definitions of temperedness and square-integrability, their invariance lemmas and Prop-valued statements; no `TemperedBlock*` module is in the closure |
| `SquareIntegrableLanglandsClassification`, task `1cb45da2-7007-4351-a694-594fb148b8d1` | No import or proof use; `Unitary.SquareIntegrable*` (unitarizability from square-integrable coefficients) enters only through the authorized reducibility closure |
| Square-integrable exhaustion, task `cd8ab97c-0b78-4bce-97c4-d307a28159a4` | No import or proof use |
| Regular exhaustion, task `bf433f0a-921a-428c-b0c0-6475438125ac` | No import or proof use; the relative regular comparison statement module only defines a proposition |
| Full `SegmentHeadProductIrreducibility`, either direction, host `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | Neither its statement module nor any proof of it is imported |
| Ze80 3.5 and 9.6, their proofs and successors; segment-socle part of `8e5b4563-0365-41c7-b134-70f2a0b36292` | Not used; the supercuspidal derivatives enter only through the separate published `SupercuspidalDerivativesProof` |
| Segment Jacquet formulas, tasks `ed48ae06-964c-4c84-9e62-978f5a953ca7`, `55ad1e10-62d8-46b7-a081-909ef0056426`, `b95105c6-f8bb-4641-ae53-2f49d1e7f034`, `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | No import or proof use |
| Socle exhaustion and ordered multisegment socle existence, tasks `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`, `23189526-80b0-4828-a6d4-7ebec2cbeef5` | No excluded conclusion used; only the generic infrastructure modules covered by `0edda612` occur |
| Segment-socle product irreducibility, linked and unlinked socle structure, socle commutation, gluing and swaps (tasks `2ae5cbe5`, `23e98d90`, `a55c4267`, `8fa9f68b`, `7ff2a1e9`, `e3634665`, `cded83f3`, `426911b4`, `66e3b87c`, `c84cd52c`, `6780b79c`) | No import or proof use |
| Analytic segment classification `aca8805b-054f-4d56-8045-12db7f623404`, special-segment square-integrability `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | No import or proof use |
| Two-supercuspidal product irreducibility or structure, including `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9` | Only the reducibility of `ρ × νρ` through `twoSupercuspidalAdjacentProductReducible`, with its published closure (which contains the Ze80 1.11(a) proof), as ruled in `2b33898b`/`ca18fd50`; `TwoSupercuspidalProductStructureProof` is not in the closure, and the length-two and Jacquet-module parts of Ze80 1.11 are not used |
| Whittaker coinvariant-finiteness conclusions | No such module is in the closure. The Whittaker modules present (Gelfand–Kazhdan multiplicity one, Iwasawa integration, Bruhat-cell distributions, character change) lie in the audited closure of `SegmentHeadTopDerivative`, on the route of `supercuspidalDerivatives` and BZ77 4.7(b) |
| Unproved statements, drafts and pending candidates | None is used as a proof; every theorem used is published |

The closure contains no `sorry`, `admit` or new axiom. Compilation and this
audit are preparation evidence; the proof requires independent review.


## Appendix: complete project import closure

The root and the seven other new modules are included. Each module corresponds to its module-path Lean file and same-stem Markdown file.

```text
Langlands.Algebra.CommutingDimensionHelpers
Langlands.Algebra.CommutingDimensionNilpotent
Langlands.Algebra.CommutingDimensionNumerics
Langlands.Algebra.CommutingDimensionPrimary
Langlands.Algebra.CommutingDimensionRecurrence
Langlands.Algebra.SandwichDimensionBoundProof
Langlands.Algebra.SandwichDimensionBoundStatement
Langlands.Algebra.SeparatedMatrixRepresentations
Langlands.Analysis.Local.CompactOpenCoverUnimodularityProof
Langlands.Analysis.Local.CompactOpenCoverUnimodularityStatement
Langlands.Analysis.Local.ModularCompactAverage
Langlands.Analysis.Local.QuotientAutomorphismProof
Langlands.Analysis.Local.QuotientAutomorphismStatement
Langlands.Analysis.Local.QuotientAverageReal
Langlands.Analysis.Local.QuotientAveragingKernel
Langlands.Analysis.Local.QuotientComplex
Langlands.Analysis.Local.QuotientFunctional
Langlands.Analysis.Local.QuotientMass
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientMeasureExistence
Langlands.Analysis.Local.QuotientMeasureExistenceStatement
Langlands.Analysis.Local.QuotientMeasurePrerequisites
Langlands.Analysis.Local.QuotientPositiveLifting
Langlands.Analysis.Local.QuotientTopology
Langlands.Analysis.Local.QuotientTranslation
Langlands.Analysis.Local.SplitKernelQuotient
Langlands.ClassFieldTheory.Local.Completion
Langlands.ClassFieldTheory.Local.FiniteArtin
Langlands.ClassFieldTheory.Local.Galois
Langlands.ClassFieldTheory.Local.Norms
Langlands.ClassFieldTheory.Local.ProfiniteReciprocityStatement
Langlands.ClassFieldTheory.Local.ReciprocityRelations
Langlands.ClassFieldTheory.Local.Transfer
Langlands.ClassFieldTheory.Local.Units
Langlands.ClassFieldTheory.Local.WeilAbelianization
Langlands.ClassFieldTheory.Local.WeilReciprocityStatement
Langlands.Combinatorics.RelationInversions
Langlands.Correspondence.AutomorphicRelations
Langlands.Correspondence.Domains
Langlands.Correspondence.LocalConventions
Langlands.Correspondence.OperationCompatibility
Langlands.Correspondence.SupercuspidalRelations
Langlands.Correspondence.UnramifiedNormalization
Langlands.Galois.FiniteField.Comparison
Langlands.Galois.FiniteField.ComparisonProof
Langlands.Galois.FiniteField.Frobenius
Langlands.Galois.Local.AbsoluteDefinitions
Langlands.Galois.Local.AbsoluteProof
Langlands.Galois.Local.AbsoluteStatement
Langlands.Galois.Local.SpectralDefinitions
Langlands.Galois.Local.SpectralProof
Langlands.Galois.Local.SpectralStatement
Langlands.Group.GL.AdjacentMergeShape
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockContractionProof
Langlands.Group.GL.BlockContractionStatement
Langlands.Group.GL.BlockDeterminant
Langlands.Group.GL.BlockIwahoriBasis
Langlands.Group.GL.BlockIwahoriBasisStatement
Langlands.Group.GL.BlockIwahoriDefinitions
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.BlockModulusHaarProof
Langlands.Group.GL.BlockModulusHaarStatement
Langlands.Group.GL.BlockScalarCenter
Langlands.Group.GL.BlockUnipotent
Langlands.Group.GL.BlockUnipotentCoordinates
Langlands.Group.GL.BlockUnipotentHaarProof
Langlands.Group.GL.BlockUnipotentHaarStatement
Langlands.Group.GL.Blocks
Langlands.Group.GL.CartanProof
Langlands.Group.GL.CartanStatement
Langlands.Group.GL.CentralQuotientTopologyProof
Langlands.Group.GL.CentralQuotientTopologyStatement
Langlands.Group.GL.CompactOpen
Langlands.Group.GL.CountabilityProof
Langlands.Group.GL.CountabilityStatement
Langlands.Group.GL.DominantExponentGeneration
Langlands.Group.GL.HeadTailBlocks
Langlands.Group.GL.IntegralSubgroup
Langlands.Group.GL.InverseTransposeIwahoriProof
Langlands.Group.GL.InverseTransposeIwahoriStatement
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedOrbitCoverageProof
Langlands.Group.GL.MirabolicMixedOrbitCoverageStatement
Langlands.Group.GL.MirabolicMixedOrbitData
Langlands.Group.GL.MirabolicMixedOrbitRadicals
Langlands.Group.GL.MirabolicMixedOrbitSectionCoefficients
Langlands.Group.GL.MirabolicMixedOrbitSections
Langlands.Group.GL.MirabolicMixedOrbitSpecializations
Langlands.Group.GL.MirabolicMixedOrbitStages
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicModularCharacterProof
Langlands.Group.GL.MirabolicModularCharacterStatement
Langlands.Group.GL.MirabolicModulusProof
Langlands.Group.GL.MirabolicModulusStatement
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.NestedRefinement
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OneBlockShape
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.PadicOppositeBlocks
Langlands.Group.GL.PadicUpperUnipotent
Langlands.Group.GL.ParabolicModularCharacter
Langlands.Group.GL.PrincipalBlockFactorizationProof
Langlands.Group.GL.PrincipalBlockFactorizationStatement
Langlands.Group.GL.PrincipalLevelDominance
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.RefinementCoordinates
Langlands.Group.GL.ReindexCongr
Langlands.Group.GL.ReverseBlocks
Langlands.Group.GL.SingleBlock
Langlands.Group.GL.SingletonBlocks
Langlands.Group.GL.Transvection
Langlands.Group.GL.TriangularParabolic
Langlands.Group.GL.UnramifiedCharacter
Langlands.Group.GL.UpperBruhatBoundaryProof
Langlands.Group.GL.UpperBruhatBoundaryStatement
Langlands.Group.GL.UpperBruhatCells
Langlands.Group.GL.UpperBruhatCoordinatesProof
Langlands.Group.GL.UpperBruhatCoordinatesStatement
Langlands.Group.GL.UpperBruhatEmbedding
Langlands.Group.GL.UpperBruhatFiltration
Langlands.Group.GL.UpperBruhatFiltrationGeometryProof
Langlands.Group.GL.UpperBruhatFiltrationGeometryStatement
Langlands.Group.GL.UpperBruhatLocalClosednessProof
Langlands.Group.GL.UpperBruhatLocalClosednessStatement
Langlands.Group.GL.UpperBruhatPivotProof
Langlands.Group.GL.UpperBruhatPivotStatement
Langlands.Group.GL.UpperBruhatProof
Langlands.Group.GL.UpperBruhatRankProof
Langlands.Group.GL.UpperBruhatRankStatement
Langlands.Group.GL.UpperBruhatStatement
Langlands.Group.GL.UpperBruhatTransposeProof
Langlands.Group.GL.UpperBruhatTransposeStatement
Langlands.Group.GL.UpperUnipotent
Langlands.Group.GL.UpperUnipotentCompactContainmentProof
Langlands.Group.GL.UpperUnipotentCompactContainmentStatement
Langlands.Group.GL.UpperUnipotentFactorizationProof
Langlands.Group.GL.UpperUnipotentFactorizationStatement
Langlands.Group.HaarModulus
Langlands.Group.LeftQuotient
Langlands.HarmonicAnalysis.AlgebraicIntegral
Langlands.HarmonicAnalysis.AlgebraicIntegrand
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.CharacterTransport
Langlands.HarmonicAnalysis.Conductor
Langlands.HarmonicAnalysis.Distribution.Basic
Langlands.HarmonicAnalysis.Distribution.BruhatFiltrationVanishingProof
Langlands.HarmonicAnalysis.Distribution.BruhatFiltrationVanishingStatement
Langlands.HarmonicAnalysis.Distribution.CharacterAverage
Langlands.HarmonicAnalysis.Distribution.CharacterAverageCovarianceProof
Langlands.HarmonicAnalysis.Distribution.CharacterAverageCovarianceStatement
Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorizationProof
Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorizationStatement
Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveProof
Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveStatement
Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionProof
Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionStatement
Langlands.HarmonicAnalysis.Distribution.ClosedSupportedDescentProof
Langlands.HarmonicAnalysis.Distribution.ClosedSupportedDescentStatement
Langlands.HarmonicAnalysis.Distribution.FiniteOrbitVanishingProof
Langlands.HarmonicAnalysis.Distribution.FiniteOrbitVanishingStatement
Langlands.HarmonicAnalysis.Distribution.GeneralLinear
Langlands.HarmonicAnalysis.Distribution.HomogeneousPositivityProof
Langlands.HarmonicAnalysis.Distribution.HomogeneousPositivityStatement
Langlands.HarmonicAnalysis.Distribution.HomogeneousVanishingProof
Langlands.HarmonicAnalysis.Distribution.HomogeneousVanishingStatement
Langlands.HarmonicAnalysis.Distribution.LocalizationProof
Langlands.HarmonicAnalysis.Distribution.LocalizationStatement
Langlands.HarmonicAnalysis.Distribution.OpenRestrictionLocalityProof
Langlands.HarmonicAnalysis.Distribution.OpenRestrictionLocalityStatement
Langlands.HarmonicAnalysis.Distribution.Subspace
Langlands.HarmonicAnalysis.Distribution.SupportedDescentCovarianceProof
Langlands.HarmonicAnalysis.Distribution.SupportedDescentCovarianceStatement
Langlands.HarmonicAnalysis.Distribution.SupportedRestriction
Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof
Langlands.HarmonicAnalysis.Distribution.TransposeInvariantStatement
Langlands.HarmonicAnalysis.FiniteProductMeasureScaling
Langlands.HarmonicAnalysis.HaarConjugacy
Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicLatticeTopology
Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof
Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement
Langlands.HarmonicAnalysis.RowFourier
Langlands.HarmonicAnalysis.RowSchwartzAction
Langlands.HarmonicAnalysis.RowTensorDecompositionProof
Langlands.HarmonicAnalysis.RowTensorDecompositionStatement
Langlands.HarmonicAnalysis.RowTestSmoothProof
Langlands.HarmonicAnalysis.RowTestSmoothStatement
Langlands.HarmonicAnalysis.SmoothWeakIntegral
Langlands.HarmonicAnalysis.TriangularTranslationProof
Langlands.HarmonicAnalysis.TriangularTranslationStatement
Langlands.LinearAlgebra.CyclicQuotientPairingProof
Langlands.LinearAlgebra.CyclicQuotientPairingStatement
Langlands.LinearAlgebra.FiniteRankTrace
Langlands.LinearAlgebra.FiniteRankTranspose
Langlands.LinearAlgebra.MatrixAEvalConjugacyProof
Langlands.LinearAlgebra.MatrixAEvalConjugacyStatement
Langlands.LinearAlgebra.MatrixCharpolyConjugacyProof
Langlands.LinearAlgebra.MatrixCharpolyConjugacyStatement
Langlands.LinearAlgebra.MatrixTransposeConjugateProof
Langlands.LinearAlgebra.MatrixTransposeConjugateStatement
Langlands.LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionProof
Langlands.LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionStatement
Langlands.LocalFactor.Euler
Langlands.LocalFactor.Euler.Definitions
Langlands.LocalFactor.Harmonic.Statement
Langlands.LocalFactor.RankOne
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.SmoothCharacterNormProof
Langlands.LocalField.SmoothCharacterNormStatement
Langlands.LocalField.Topology
Langlands.LocalField.Uniformizer
Langlands.Representation.Category.Abelian
Langlands.Representation.Category.Basic
Langlands.Representation.Category.ClassInvariants
Langlands.Representation.Category.ConstituentDichotomy
Langlands.Representation.Category.ConstituentDichotomyStatement
Langlands.Representation.Category.Contragredient
Langlands.Representation.Category.FiniteIndexRestriction
Langlands.Representation.Category.FiniteIndexSemisimplicity
Langlands.Representation.Category.FiniteIndexSemisimplicityStatement
Langlands.Representation.Category.RestrictionSubquotients
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Category.UniverseLift
Langlands.Representation.Character.Basic
Langlands.Representation.Character.SeparationProof
Langlands.Representation.Character.SeparationStatement
Langlands.Representation.Character.TransportProof
Langlands.Representation.Character.TransportStatement
Langlands.Representation.Classification.CanonicalConstituents
Langlands.Representation.Classification.CommonImageMultiplicityOneProof
Langlands.Representation.Classification.CommonImageMultiplicityOneStatement
Langlands.Representation.Classification.ConstituentCompatibility
Langlands.Representation.Classification.ConstituentRelations
Langlands.Representation.Classification.Cosocle
Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement
Langlands.Representation.Classification.CuspidalJacquetFunctorExactnessProof
Langlands.Representation.Classification.CuspidalJacquetFunctorExactnessStatement
Langlands.Representation.Classification.CuspidalJacquetFunctors
Langlands.Representation.Classification.CuspidalJacquetMultiplicityProof
Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
Langlands.Representation.Classification.CuspidalProductContragredient
Langlands.Representation.Classification.CuspidalProductDerivativeQuotientSupport
Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftProof
Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftStatement
Langlands.Representation.Classification.Essential
Langlands.Representation.Classification.ExponentFamily
Langlands.Representation.Classification.HeadQuotientCriterionProof
Langlands.Representation.Classification.HeadQuotientCriterionStatement
Langlands.Representation.Classification.IrreducibleProductEmbedding
Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement
Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
Langlands.Representation.Classification.IrreducibleTwoFactorProductSwapProof
Langlands.Representation.Classification.IrreducibleTwoFactorProductSwapStatement
Langlands.Representation.Classification.LanglandsData
Langlands.Representation.Classification.MirabolicDerivativeContragredient
Langlands.Representation.Classification.MultiplicityOneConstituentProof
Langlands.Representation.Classification.MultiplicityOneConstituentStatement
Langlands.Representation.Classification.NonadjacentAssembly
Langlands.Representation.Classification.NonadjacentLeibnizPieces
Langlands.Representation.Classification.NonadjacentSpecialization
Langlands.Representation.Classification.NonadjacentTwoBlock
Langlands.Representation.Classification.NormalizedProductFiniteLengthProof
Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement
Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof
Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationStatement
Langlands.Representation.Classification.OppositeJacquetQuotientDetectionProof
Langlands.Representation.Classification.OppositeJacquetQuotientDetectionStatement
Langlands.Representation.Classification.OppositeJacquetReciprocity
Langlands.Representation.Classification.OppositeSupportJacquetAdapter
Langlands.Representation.Classification.RelativeGenericityStatement
Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement
Langlands.Representation.Classification.RelativeRegularComparisonStatement
Langlands.Representation.Classification.SegmentConstituentStatement
Langlands.Representation.Classification.SegmentCuspidalContent
Langlands.Representation.Classification.SegmentDecreasingCuspidalProduct
Langlands.Representation.Classification.SegmentHeadDecreasingSocle
Langlands.Representation.Classification.SegmentHeadDerivativeSupportLengthTwo
Langlands.Representation.Classification.SegmentHeadDerivativeSupportTruncationProof
Langlands.Representation.Classification.SegmentHeadDerivativeSupportTruncationStatement
Langlands.Representation.Classification.SegmentHeadProductFiniteness
Langlands.Representation.Classification.SegmentHeadSupportCons
Langlands.Representation.Classification.SegmentHeadSupportGeneric
Langlands.Representation.Classification.SegmentHeadSupportLeftExact
Langlands.Representation.Classification.SegmentHeadSupportLeibniz
Langlands.Representation.Classification.SegmentHeadSupportSplit
Langlands.Representation.Classification.SegmentHeadSupportStep
Langlands.Representation.Classification.SegmentHeadTopDerivative
Langlands.Representation.Classification.SegmentInductionAdmissibilityProof
Langlands.Representation.Classification.SegmentInductionAdmissibilityStatement
Langlands.Representation.Classification.SegmentJacquetMultiplicityProof
Langlands.Representation.Classification.SegmentJacquetMultiplicityStatement
Langlands.Representation.Classification.SegmentJacquetReversal
Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof
Langlands.Representation.Classification.SegmentTensorReversalProof
Langlands.Representation.Classification.SegmentTensorReversalStatement
Langlands.Representation.Classification.SegmentTensorStabilizerProof
Langlands.Representation.Classification.SegmentTensorStabilizerStatement
Langlands.Representation.Classification.SegmentTruncationObstructionStatement
Langlands.Representation.Classification.Segments
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalContragredient
Langlands.Representation.Classification.SupercuspidalContragredientAux
Langlands.Representation.Classification.SupercuspidalContragredientProof
Langlands.Representation.Classification.SupercuspidalContragredientStatement
Langlands.Representation.Classification.SupercuspidalDerivativeVanishing
Langlands.Representation.Classification.SupercuspidalDerivativesProof
Langlands.Representation.Classification.SupercuspidalDerivativesStatement
Langlands.Representation.Classification.SupercuspidalSupport
Langlands.Representation.Classification.SupercuspidalSupportStatement
Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof
Langlands.Representation.Classification.SupercuspidalTopDerivative
Langlands.Representation.Classification.SupercuspidalTwist
Langlands.Representation.Classification.Tempered
Langlands.Representation.Classification.TemperedInductionStatement
Langlands.Representation.Classification.TemperedSupportStatement
Langlands.Representation.Classification.TwistedProductCharacterTwistProof
Langlands.Representation.Classification.TwoBlockExponentNonUnitarizabilityProof
Langlands.Representation.Classification.TwoBlockExponentNonUnitarizabilityStatement
Langlands.Representation.Classification.TwoSupercuspidalAdjacentReducibilityProof
Langlands.Representation.Classification.TwoSupercuspidalAdjacentReducibilityStatement
Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge
Langlands.Representation.Classification.TwoSupercuspidalDerivativeBridge
Langlands.Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof
Langlands.Representation.Classification.TwoSupercuspidalProductDualTwist
Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement
Langlands.Representation.Classification.UnitaryGenericCompatibilityStatement
Langlands.Representation.Classification.UpperCuspidalJacquetMultiplicityProof
Langlands.Representation.Classification.UpperCuspidalJacquetMultiplicityStatement
Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionProof
Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionStatement
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.OrbitMeanTranslation
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Compact.SurjectivityProof
Langlands.Representation.Compact.SurjectivityStatement
Langlands.Representation.CompactCoefficient.AdmissibleComplement
Langlands.Representation.CompactCoefficient.AdmissibleLifting
Langlands.Representation.CompactCoefficient.AdmissibleRetraction
Langlands.Representation.CompactCoefficient.AmbientProjector
Langlands.Representation.CompactCoefficient.Classes
Langlands.Representation.CompactCoefficient.ConditionalProjection
Langlands.Representation.CompactCoefficient.FixedLevelFiniteness
Langlands.Representation.CompactCoefficient.FixedVectorsFiniteDimensional
Langlands.Representation.CompactCoefficient.GroupTransport
Langlands.Representation.CompactCoefficient.Isotypic
Langlands.Representation.CompactCoefficient.IsotypicTransport
Langlands.Representation.CompactCoefficient.NormalSubgroupDecomposition
Langlands.Representation.CompactCoefficient.OrthogonalProjectorFamily
Langlands.Representation.CompactCoefficient.SelectedAssembly
Langlands.Representation.CompactCoefficient.SelectedBlock
Langlands.Representation.CompactCoefficient.SelectedConjugation
Langlands.Representation.CompactCoefficient.SelectedCoverage
Langlands.Representation.CompactCoefficient.SelectedProjector
Langlands.Representation.CompactCoefficient.SemisimplicityProof
Langlands.Representation.CompactCoefficient.SemisimplicityStatement
Langlands.Representation.CompactCoefficient.TotalCompactness
Langlands.Representation.CompactCoefficient.TotalProjector
Langlands.Representation.Conductor.Congruence
Langlands.Representation.Conductor.Definitions
Langlands.Representation.Conductor.PrincipalCongruence
Langlands.Representation.Conductor.PrincipalCongruenceBasisProof
Langlands.Representation.Conductor.PrincipalCongruenceBasisStatement
Langlands.Representation.CuspidalSupport.AssociatedAssembly
Langlands.Representation.CuspidalSupport.AssociatedConditional
Langlands.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof
Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesProof
Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement
Langlands.Representation.CuspidalSupport.AssociatedProof
Langlands.Representation.CuspidalSupport.AssociatedRankZero
Langlands.Representation.CuspidalSupport.AssociationForwardHomProof
Langlands.Representation.CuspidalSupport.AssociationForwardHomSupport
Langlands.Representation.CuspidalSupport.AssociationForwardStatement
Langlands.Representation.CuspidalSupport.AssociationLawsProof
Langlands.Representation.CuspidalSupport.AssociationLawsStatement
Langlands.Representation.CuspidalSupport.AssociationReduction
Langlands.Representation.CuspidalSupport.AssociationReverseProof
Langlands.Representation.CuspidalSupport.AssociationReverseStatement
Langlands.Representation.CuspidalSupport.BlockMap
Langlands.Representation.CuspidalSupport.BlockPermutation
Langlands.Representation.CuspidalSupport.BlockWeylTransport
Langlands.Representation.CuspidalSupport.CentralShift
Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessProof
Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction
Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement
Langlands.Representation.CuspidalSupport.ConstituentComplement
Langlands.Representation.CuspidalSupport.ConstituentComplementStatement
Langlands.Representation.CuspidalSupport.ConstituentFiniteTypes
Langlands.Representation.CuspidalSupport.ConstituentInduction
Langlands.Representation.CuspidalSupport.ConstituentInductionStatement
Langlands.Representation.CuspidalSupport.ConstituentProof
Langlands.Representation.CuspidalSupport.ConstituentRankZero
Langlands.Representation.CuspidalSupport.ConstituentSemisimple
Langlands.Representation.CuspidalSupport.ConstituentSemisimpleStatement
Langlands.Representation.CuspidalSupport.CuspidalBlockIsolationProof
Langlands.Representation.CuspidalSupport.CuspidalBlockIsolationStatement
Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
Langlands.Representation.CuspidalSupport.CuspidalTensorProof
Langlands.Representation.CuspidalSupport.CuspidalTensorStatement
Langlands.Representation.CuspidalSupport.CuspidalityComparisonProof
Langlands.Representation.CuspidalSupport.CuspidalityComparisonStatement
Langlands.Representation.CuspidalSupport.DeterminantUnit
Langlands.Representation.CuspidalSupport.DeterminantUnitCartanSupport
Langlands.Representation.CuspidalSupport.DeterminantUnitCentralCompactnessProof
Langlands.Representation.CuspidalSupport.DeterminantUnitCentralCompactnessStatement
Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureProof
Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureStatement
Langlands.Representation.CuspidalSupport.DeterminantUnitFiniteRestriction
Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof
Langlands.Representation.CuspidalSupport.DeterminantUnitStructureStatement
Langlands.Representation.CuspidalSupport.DistinctTensorStabilizerProof
Langlands.Representation.CuspidalSupport.DistinctTensorStabilizerStatement
Langlands.Representation.CuspidalSupport.DualAveraging
Langlands.Representation.CuspidalSupport.FiltrationQuasicuspidality
Langlands.Representation.CuspidalSupport.FiniteBlockShapes
Langlands.Representation.CuspidalSupport.GroupTransport
Langlands.Representation.CuspidalSupport.HarishChandraAssembly
Langlands.Representation.CuspidalSupport.HarishChandraBoundaryProof
Langlands.Representation.CuspidalSupport.HarishChandraBoundaryStatement
Langlands.Representation.CuspidalSupport.HarishChandraConverseProof
Langlands.Representation.CuspidalSupport.HarishChandraConverseStatement
Langlands.Representation.CuspidalSupport.HarishChandraForwardProof
Langlands.Representation.CuspidalSupport.HarishChandraStatement
Langlands.Representation.CuspidalSupport.InducedJacquetCount
Langlands.Representation.CuspidalSupport.InducedJacquetEvaluation
Langlands.Representation.CuspidalSupport.IrreducibleLeviAdmissibilityProof
Langlands.Representation.CuspidalSupport.IrreducibleLeviAdmissibilityStatement
Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof
Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthStatement
Langlands.Representation.CuspidalSupport.JacquetInductionStatement
Langlands.Representation.CuspidalSupport.JacquetLengthDetector
Langlands.Representation.CuspidalSupport.JacquetSubquotientProof
Langlands.Representation.CuspidalSupport.JacquetSubquotientStatement
Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers
Langlands.Representation.CuspidalSupport.JacquetVanishingSmoothPieces
Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof
Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationStatement
Langlands.Representation.CuspidalSupport.LeviAssociation
Langlands.Representation.CuspidalSupport.LeviCompactPart
Langlands.Representation.CuspidalSupport.LeviDecompositionAssembly
Langlands.Representation.CuspidalSupport.LeviDefinitions
Langlands.Representation.CuspidalSupport.LeviGapVanishing
Langlands.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof
Langlands.Representation.CuspidalSupport.LeviSplitContraction
Langlands.Representation.CuspidalSupport.LeviTensorFactorizationProof
Langlands.Representation.CuspidalSupport.LeviTensorFactorizationStatement
Langlands.Representation.CuspidalSupport.LeviTensorReflectionProof
Langlands.Representation.CuspidalSupport.LeviTensorReflectionStatement
Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
Langlands.Representation.CuspidalSupport.MinimalJacquetProof
Langlands.Representation.CuspidalSupport.MinimalJacquetStatement
Langlands.Representation.CuspidalSupport.MinimalRefinedJacquetProof
Langlands.Representation.CuspidalSupport.MinimalRefinedJacquetStatement
Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof
Langlands.Representation.CuspidalSupport.NaturalProjectorDecomposition
Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof
Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof
Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement
Langlands.Representation.CuspidalSupport.PointwiseProjectorSum
Langlands.Representation.CuspidalSupport.ProperInductionMaps
Langlands.Representation.CuspidalSupport.ProperInductionProof
Langlands.Representation.CuspidalSupport.ProperInductionStatement
Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof
Langlands.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement
Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement
Langlands.Representation.CuspidalSupport.RefinedQuasicuspidalEmbeddingProof
Langlands.Representation.CuspidalSupport.RefinedQuasicuspidalEmbeddingStatement
Langlands.Representation.CuspidalSupport.StandardJacquetComparisonProof
Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
Langlands.Representation.CuspidalSupport.TotalConjugatingCountStatement
Langlands.Representation.CuspidalSupport.WholeLeviTransport
Langlands.Representation.CuspidalSupport.ZeroRankEmbeddingProof
Langlands.Representation.Derivative.DerivativeEquivTransport
Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof
Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessStatement
Langlands.Representation.Derivative.GeneralLinearDerivativeFiniteLengthProof
Langlands.Representation.Derivative.GeneralLinearDerivativeFiniteLengthStatement
Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizBoundary
Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof
Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.LeftMixedProductDerivativeProof
Langlands.Representation.Derivative.LeftMixedProductHigher
Langlands.Representation.Derivative.LeftMixedProductHomogeneityProof
Langlands.Representation.Derivative.LeftMixedProductHomogeneityStatement
Langlands.Representation.Derivative.LeftMixedProductPhiHatIterate
Langlands.Representation.Derivative.LeftMixedProductVanishing
Langlands.Representation.Derivative.LeftMixedProductZeroRank
Langlands.Representation.Derivative.LeibnizIndices
Langlands.Representation.Derivative.LeibnizPieceCompat
Langlands.Representation.Derivative.LeibnizPositiveGluing
Langlands.Representation.Derivative.LeibnizQuotientPiece
Langlands.Representation.Derivative.LeibnizRankZeroBoundary
Langlands.Representation.Derivative.LeibnizRankZeroGluing
Langlands.Representation.Derivative.LeibnizRestrictionCompat
Langlands.Representation.Derivative.LeibnizRestrictionExact
Langlands.Representation.Derivative.LeibnizZeroFirstPiece
Langlands.Representation.Derivative.LevelCalculus
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDerivativeDetectionProof
Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement
Langlands.Representation.Derivative.MirabolicDerivativeUnitInjective
Langlands.Representation.Derivative.MirabolicDerivativeVanishing
Langlands.Representation.Derivative.MirabolicDeterminant
Langlands.Representation.Derivative.MirabolicHighestDerivativeDescent
Langlands.Representation.Derivative.MirabolicHighestDerivativePairingProof
Langlands.Representation.Derivative.MirabolicHighestDerivativePairingStatement
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMinusExactnessProof
Langlands.Representation.Derivative.MirabolicMinusExactnessStatement
Langlands.Representation.Derivative.MirabolicMinusNormalization
Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof
Langlands.Representation.Derivative.MirabolicMinusPairingTransferStatement
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
Langlands.Representation.Derivative.MirabolicPhiMinusMackey
Langlands.Representation.Derivative.MirabolicPhiMinusNondegeneratePairing
Langlands.Representation.Derivative.MirabolicPlus
Langlands.Representation.Derivative.MirabolicPlusNormalization
Langlands.Representation.Derivative.MirabolicProductMinusBoundary
Langlands.Representation.Derivative.MirabolicProductMinusCompatibility
Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhi
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCompactComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHaar
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHostTransport
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiIdentityComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiInductionNormalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiLocalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiMackeyLocalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceAction
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiStagesComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPsi
Langlands.Representation.Derivative.MirabolicProductMinusLeftPsiInduction
Langlands.Representation.Derivative.MirabolicProductMinusPhiKernelComparison
Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary
Langlands.Representation.Derivative.MirabolicProductMinusRightPhi
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiAssembly
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycle
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleGroups
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentity
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityGroups
Langlands.Representation.Derivative.MirabolicProductMinusRightPsi
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiGroups
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiZero
Langlands.Representation.Derivative.MirabolicProductRestriction
Langlands.Representation.Derivative.MirabolicProductRestrictionCasts
Langlands.Representation.Derivative.MirabolicProductRestrictionFactors
Langlands.Representation.Derivative.MirabolicProductRestrictionMackey
Langlands.Representation.Derivative.MirabolicProductRestrictionOrbits
Langlands.Representation.Derivative.MirabolicProductRestrictionStabilizers
Langlands.Representation.Derivative.MirabolicProductRestrictionStatement
Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
Langlands.Representation.Derivative.MirabolicSmoothPhiPlus
Langlands.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction
Langlands.Representation.Derivative.MirabolicSmoothPhiPlusIterate
Langlands.Representation.Derivative.MirabolicSmoothPhiPlusProduct
Langlands.Representation.Derivative.MixedProductDerivativeStatement
Langlands.Representation.Derivative.MixedProductRankCast
Langlands.Representation.Derivative.OrderRecursion
Langlands.Representation.Derivative.OrderedCuspidalProductHeadShift
Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof
Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyStatement
Langlands.Representation.Derivative.OrderedCuspidalProductTwistOne
Langlands.Representation.Derivative.Partial
Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonProof
Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonStatement
Langlands.Representation.Derivative.PartialDerivativeJacquetLHS
Langlands.Representation.Derivative.PartialDerivativeJacquetNormalization
Langlands.Representation.Derivative.PartialDerivativeJacquetRHS
Langlands.Representation.Derivative.PartialDerivativeJacquetRHSComparison
Langlands.Representation.Derivative.PartialLocalizationCharacter
Langlands.Representation.Derivative.PartialLocalizationData
Langlands.Representation.Derivative.ProductDerivativesFiniteLength
Langlands.Representation.Derivative.ProductVanishing
Langlands.Representation.Derivative.RankCastCompat
Langlands.Representation.Derivative.RestrictedProductLevel
Langlands.Representation.Derivative.RestrictionBridge
Langlands.Representation.Derivative.RightMixedLevel
Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationProof
Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement
Langlands.Representation.Derivative.RightMixedProductDerivativePositive
Langlands.Representation.Derivative.RightMixedProductPhiMinusDetectionProof
Langlands.Representation.Derivative.RightMixedProductZeroRank
Langlands.Representation.Derivative.ShortExactFunctorLaws
Langlands.Representation.Derivative.TopLine
Langlands.Representation.Derivative.TopLocalizationData
Langlands.Representation.Derivative.ZeroRankTensor
Langlands.Representation.Dual.Definitions
Langlands.Representation.Exponents.Central
Langlands.Representation.Exponents.ComplexTwistFamilies
Langlands.Representation.Exponents.DualJacquet
Langlands.Representation.Exponents.DualJacquetStatement
Langlands.Representation.Exponents.Jacquet
Langlands.Representation.Exponents.NilpotenceIndex
Langlands.Representation.Exponents.ParabolicPair
Langlands.Representation.Exponents.RealTwistFamilies
Langlands.Representation.Exponents.SupportedRegularMultiplicityBranchObstructionStatement
Langlands.Representation.Exponents.UnitaryDualJacquetSupportAdapters
Langlands.Representation.Exponents.WeylBranchPiecesStatement
Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
Langlands.Representation.Filtration.CoinvariantVanishingStatement
Langlands.Representation.Filtration.CommonSubquotientStatement
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.FactorMatchingPullback
Langlands.Representation.Filtration.FiniteFamilyMultiplicityProof
Langlands.Representation.Filtration.FiniteFamilyMultiplicityStatement
Langlands.Representation.Filtration.FunctorLengthTwoDetection
Langlands.Representation.Filtration.GluedFamily
Langlands.Representation.Filtration.GradedRefinementProof
Langlands.Representation.Filtration.GradedRefinementStatement
Langlands.Representation.Filtration.IntervalLiftProof
Langlands.Representation.Filtration.IntervalLiftStatement
Langlands.Representation.Filtration.InvariantBilinear
Langlands.Representation.Filtration.InvariantBilinearBounds
Langlands.Representation.Filtration.InvariantBilinearSubquotientBounds
Langlands.Representation.Filtration.IrreducibleMultiplicityProof
Langlands.Representation.Filtration.IrreducibleMultiplicityStatement
Langlands.Representation.Filtration.IsoTransport
Langlands.Representation.Filtration.JordanHolderComparisonProof
Langlands.Representation.Filtration.JordanHolderProof
Langlands.Representation.Filtration.JordanHolderStatement
Langlands.Representation.Filtration.JordanHolderTransportProof
Langlands.Representation.Filtration.LengthCriterionProof
Langlands.Representation.Filtration.LengthCriterionStatement
Langlands.Representation.Filtration.LengthTwoMatching
Langlands.Representation.Filtration.LengthTwoMatchingStatement
Langlands.Representation.Filtration.MultiplicityAdditivityProof
Langlands.Representation.Filtration.MultiplicityAdditivityStatement
Langlands.Representation.Filtration.MultiplicityIndependenceProof
Langlands.Representation.Filtration.MultiplicityStatement
Langlands.Representation.Filtration.MultiplicityTransportProof
Langlands.Representation.Filtration.MultiplicityTransportStatement
Langlands.Representation.Filtration.NonzeroHomCommonSubquotientProof
Langlands.Representation.Filtration.NonzeroHomCommonSubquotientStatement
Langlands.Representation.Filtration.ObjectDefinitions
Langlands.Representation.Filtration.ObjectTransport
Langlands.Representation.Filtration.OneStep
Langlands.Representation.Filtration.Precomposition
Langlands.Representation.Filtration.QuasicuspidalVanishingProof
Langlands.Representation.Filtration.QuotientFirstIso
Langlands.Representation.Filtration.QuotientTail
Langlands.Representation.Filtration.RepresentationLength
Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionProof
Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionStatement
Langlands.Representation.Filtration.SimpleSubquotientFactorProof
Langlands.Representation.Filtration.SimpleSubquotientFactorStatement
Langlands.Representation.Filtration.SmoothDualEvaluation
Langlands.Representation.Filtration.Splicing
Langlands.Representation.Filtration.Splicing.Basic
Langlands.Representation.Filtration.SubquotientAlgebraProof
Langlands.Representation.Filtration.SubquotientAlgebraStatement
Langlands.Representation.Filtration.SubsingletonProof
Langlands.Representation.Filtration.Transport
Langlands.Representation.Filtration.VanishingStatement
Langlands.Representation.Filtration.ZeroFactorDeletionProof
Langlands.Representation.Filtration.ZeroFactorDeletionStatement
Langlands.Representation.Geometric.BlockIntersectionSplitting
Langlands.Representation.Geometric.BlockSixDecomposableProof
Langlands.Representation.Geometric.BlockSixDecomposableStatement
Langlands.Representation.Geometric.BruhatDescent
Langlands.Representation.Geometric.BruhatMatrixExistenceProof
Langlands.Representation.Geometric.BruhatMatrixStatement
Langlands.Representation.Geometric.BruhatWeylReflectionProof
Langlands.Representation.Geometric.ClosedSubgroupAssembly
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
Langlands.Representation.Geometric.ClosedSubgroupMackeyProof
Langlands.Representation.Geometric.ClosedSubgroupStatement
Langlands.Representation.Geometric.CoarseLeviReversal
Langlands.Representation.Geometric.CompactOrbitRestriction
Langlands.Representation.Geometric.CompactSmoothComparison
Langlands.Representation.Geometric.ConditionalAssembly
Langlands.Representation.Geometric.CorrectionSubgroupCoordinates
Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarProof
Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarStatement
Langlands.Representation.Geometric.CosetAction
Langlands.Representation.Geometric.CosetOrbitHomeomorph
Langlands.Representation.Geometric.CosetOrbitOrdering
Langlands.Representation.Geometric.FlattenedLevi
Langlands.Representation.Geometric.GeneralCorrectionCharacters
Langlands.Representation.Geometric.GeneralIntersectionNormalizers
Langlands.Representation.Geometric.GeneralIntersections
Langlands.Representation.Geometric.GeometricLemmaProof
Langlands.Representation.Geometric.GeometricLemmaStatement
Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterProof
Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterStatement
Langlands.Representation.Geometric.IntersectionLeviModulusBalance
Langlands.Representation.Geometric.IntersectionTransport
Langlands.Representation.Geometric.MonotoneBlocksProof
Langlands.Representation.Geometric.MonotoneBlocksStatement
Langlands.Representation.Geometric.OrbitRepresentatives
Langlands.Representation.Geometric.OrbitRestriction
Langlands.Representation.Geometric.OrbitSectionExtensionProof
Langlands.Representation.Geometric.OrbitSectionExtensionStatement
Langlands.Representation.Geometric.PadicCorrectionCancellationProof
Langlands.Representation.Geometric.PadicCorrectionCancellationStatement
Langlands.Representation.Geometric.PadicParabolicBruhatProof
Langlands.Representation.Geometric.ParabolicOrbitCoefficientComparison
Langlands.Representation.Geometric.ParabolicOrbitCompactComparison
Langlands.Representation.Geometric.ParabolicOrbitComparisonData
Langlands.Representation.Geometric.ParabolicOrbitHaarComparison
Langlands.Representation.Geometric.ParabolicOrbitHaarRatio
Langlands.Representation.Geometric.ParabolicOrbitHaarTransport
Langlands.Representation.Geometric.ParabolicOrbitInductionTransport
Langlands.Representation.Geometric.ParabolicOrbitJacquet
Langlands.Representation.Geometric.ParabolicOrbitJacquetProof
Langlands.Representation.Geometric.ParabolicOrbitJacquetStatement
Langlands.Representation.Geometric.ParabolicOrbitMeasureData
Langlands.Representation.Geometric.ParabolicOrbitNestedAction
Langlands.Representation.Geometric.ParabolicOrbitNormalization
Langlands.Representation.Geometric.ParabolicOrbitNormalizedCoefficient
Langlands.Representation.Geometric.ParabolicOrbitSectionComparison
Langlands.Representation.Geometric.ParabolicOrbitStagesCoefficient
Langlands.Representation.Geometric.ParabolicSupportFiltration
Langlands.Representation.Geometric.ParabolicSupportGradedProof
Langlands.Representation.Geometric.ParabolicSupportGradedStatement
Langlands.Representation.Geometric.ParabolicSupportJacquetProof
Langlands.Representation.Geometric.ParabolicSupportJacquetStatement
Langlands.Representation.Geometric.ParabolicSupportTransport
Langlands.Representation.Geometric.RefinedPositiveCharacter
Langlands.Representation.Geometric.RefinementDefinitions
Langlands.Representation.Geometric.RefinementFunctors
Langlands.Representation.Geometric.RefinementUniqueness
Langlands.Representation.Geometric.SmoothSupportFiltration
Langlands.Representation.Geometric.StandardIntersectionsProof
Langlands.Representation.Geometric.WeylDefinitions
Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
Langlands.Representation.Geometric.WeylStatement
Langlands.Representation.Geometric.WeylUniquenessProof
Langlands.Representation.Geometric.WeylUniquenessStatement
Langlands.Representation.Hecke.ActionIntegrand
Langlands.Representation.Hecke.ActionLocalUnits
Langlands.Representation.Hecke.ActionProjection
Langlands.Representation.Hecke.AntiPullback
Langlands.Representation.Hecke.CommonInvarianceProof
Langlands.Representation.Hecke.CommonInvarianceStatement
Langlands.Representation.Hecke.Convolution
Langlands.Representation.Hecke.Corner
Langlands.Representation.Hecke.CornerAction
Langlands.Representation.Hecke.CornerDetermination
Langlands.Representation.Hecke.DoubleCoset
Langlands.Representation.Hecke.DoubleCosetSandwich
Langlands.Representation.Hecke.FiniteRankAction
Langlands.Representation.Hecke.IntegratedAction
Langlands.Representation.Hecke.IntegratedConvolution
Langlands.Representation.Hecke.NormalizedIndicator
Langlands.Representation.Hecke.SmoothTranspose
Langlands.Representation.Hecke.TestFunction
Langlands.Representation.Induction.BinaryPositiveCompact
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockCharacterAbsorption
Langlands.Representation.Induction.BlockEquivalence
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.CharacterTwistProof
Langlands.Representation.Induction.CompactAutomorphism
Langlands.Representation.Induction.CompactAutomorphismIntegralProof
Langlands.Representation.Induction.CompactAutomorphismIntegralStatement
Langlands.Representation.Induction.CompactBilinearPairing
Langlands.Representation.Induction.CompactCoinvariantBijectivityProof
Langlands.Representation.Induction.CompactCoinvariantBijectivityStatement
Langlands.Representation.Induction.CompactCoinvariantIntegral
Langlands.Representation.Induction.CompactCoinvariantLocalInverseProof
Langlands.Representation.Induction.CompactCoinvariantLocalInverseStatement
Langlands.Representation.Induction.CompactIntegralForm
Langlands.Representation.Induction.CompactLocalSection
Langlands.Representation.Induction.CompactLocalSectionSpanningProof
Langlands.Representation.Induction.CompactLocalSectionSpanningStatement
Langlands.Representation.Induction.CompactLocallyConstant
Langlands.Representation.Induction.CompactPairingDuality
Langlands.Representation.Induction.CompactQuotientCutoff
Langlands.Representation.Induction.CompactQuotientProof
Langlands.Representation.Induction.CompactScalarProof
Langlands.Representation.Induction.CompactScalarStatement
Langlands.Representation.Induction.CompactSurjectivityProof
Langlands.Representation.Induction.CompactSurjectivityStatement
Langlands.Representation.Induction.CompactTransitivityProof
Langlands.Representation.Induction.CompactTransitivityStatement
Langlands.Representation.Induction.ConjugateParabolic
Langlands.Representation.Induction.CovariantRescaling
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Equivalences
Langlands.Representation.Induction.FiniteProductTensor
Langlands.Representation.Induction.FiniteProductTensorBijectiveProof
Langlands.Representation.Induction.FiniteProductTensorBijectiveStatement
Langlands.Representation.Induction.HeterogeneousConstruction
Langlands.Representation.Induction.HeterogeneousPairs
Langlands.Representation.Induction.InverseTranspose
Langlands.Representation.Induction.NormalCoinvariantKernelProof
Langlands.Representation.Induction.NormalCoinvariantKernelStatement
Langlands.Representation.Induction.NormalCoinvariantMap
Langlands.Representation.Induction.NormalCoinvariantProof
Langlands.Representation.Induction.NormalCoinvariantStatement
Langlands.Representation.Induction.NormalSplitComparison
Langlands.Representation.Induction.NormalizedIntegralForm
Langlands.Representation.Induction.OppositeParabolic
Langlands.Representation.Induction.OppositeProductReversalProof
Langlands.Representation.Induction.OppositeProductReversalStatement
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.PiScalarIntegral
Langlands.Representation.Induction.SingleBlock
Langlands.Representation.Induction.SplitKernelCharacter
Langlands.Representation.Induction.SplitKernelCharacterExtension
Langlands.Representation.Induction.SplitKernelCompact
Langlands.Representation.Induction.SplitKernelCovariance
Langlands.Representation.Induction.SplitKernelEquivariant
Langlands.Representation.Induction.SplitKernelHaarTrivial
Langlands.Representation.Induction.SplitKernelIntegral
Langlands.Representation.Induction.SplitKernelLocalizationData
Langlands.Representation.Induction.SplitKernelSectionAction
Langlands.Representation.Induction.SplitQuotientProof
Langlands.Representation.Induction.SplitQuotientStatement
Langlands.Representation.Induction.SplitStagesCharacterComparison
Langlands.Representation.Induction.SplitStagesCharacterComparisonStatement
Langlands.Representation.Induction.SplitStagesCharacterIntegrand
Langlands.Representation.Induction.SplitStagesComparison
Langlands.Representation.Induction.SplitStagesRetraction
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.Induction.SurjectivityProof
Langlands.Representation.Induction.SurjectivityStatement
Langlands.Representation.Jacquet.BlockCompressionProof
Langlands.Representation.Jacquet.BlockCompressionStatement
Langlands.Representation.Jacquet.BlockPowerKernelProof
Langlands.Representation.Jacquet.CanonicalLiftBijectivityProof
Langlands.Representation.Jacquet.CanonicalLiftDefinitions
Langlands.Representation.Jacquet.CanonicalLiftGroupTransportProof
Langlands.Representation.Jacquet.CanonicalLiftGroupTransportStatement
Langlands.Representation.Jacquet.CanonicalLiftIntertwinerNaturalityProof
Langlands.Representation.Jacquet.CanonicalLiftIntertwinerNaturalityStatement
Langlands.Representation.Jacquet.CanonicalLiftStatement
Langlands.Representation.Jacquet.CharacterAveraging
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.CompactCompressionStableDualityProof
Langlands.Representation.Jacquet.CompactCompressionStableDualityStatement
Langlands.Representation.Jacquet.CompressionStabilizationProof
Langlands.Representation.Jacquet.CompressionStabilizationStatement
Langlands.Representation.Jacquet.ExactProof
Langlands.Representation.Jacquet.ExactStatement
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.LocalizationExactnessProof
Langlands.Representation.Jacquet.LocalizationExactnessStatement
Langlands.Representation.Jacquet.LocalizationTower
Langlands.Representation.Jacquet.LocalizationTransport
Langlands.Representation.Jacquet.Normalized
Langlands.Representation.Jacquet.OppositeCanonicalLiftProof
Langlands.Representation.Jacquet.OppositeCanonicalLiftStatement
Langlands.Representation.Jacquet.Parabolic
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.ReciprocityProof
Langlands.Representation.Jacquet.ReciprocityStatement
Langlands.Representation.Jacquet.RefinedOppositeCanonicalLiftProof
Langlands.Representation.Jacquet.RefinedOppositeCanonicalLiftStatement
Langlands.Representation.Jacquet.RefinedOppositeCompressionProof
Langlands.Representation.Jacquet.RefinedOppositeCompressionStatement
Langlands.Representation.Jacquet.RefinedOppositePowerKernelProof
Langlands.Representation.Jacquet.RefinedOppositeStableImageProof
Langlands.Representation.Jacquet.RefinedUpperCanonicalLiftProof
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.Jacquet.StablePairingProof
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.HermitianProduct
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.MatrixCoefficient.ModuloCenter
Langlands.Representation.MatrixCoefficient.NormRegularityProof
Langlands.Representation.MatrixCoefficient.NormRegularityStatement
Langlands.Representation.Mirabolic.LeftMixedProductSuccessor
Langlands.Representation.Mirabolic.MixedProducts
Langlands.Representation.OrbitSpan
Langlands.Representation.Parabolic.AdmissibilityStatement
Langlands.Representation.Parabolic.ComposedFunctors
Langlands.Representation.Parabolic.ExactnessReciprocityStatement
Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation
Langlands.Representation.Parabolic.GeometricPrerequisitesStatement
Langlands.Representation.Parabolic.HeadTailProductInduction
Langlands.Representation.Parabolic.InductionExactnessProof
Langlands.Representation.Parabolic.InductionFactorMatchingProof
Langlands.Representation.Parabolic.InductionFactorMatchingStatement
Langlands.Representation.Parabolic.InductionSubrepresentation
Langlands.Representation.Parabolic.InverseTransposeProductProof
Langlands.Representation.Parabolic.InverseTransposeProductStatement
Langlands.Representation.Parabolic.LeviBridges
Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof
Langlands.Representation.Parabolic.NaturalFirstAdjointness
Langlands.Representation.Parabolic.NaturalInductionDualityFromScalar
Langlands.Representation.Parabolic.NaturalInductionDualityProof
Langlands.Representation.Parabolic.NaturalInductionDualityStatement
Langlands.Representation.Parabolic.NaturalJacquetDualityProof
Langlands.Representation.Parabolic.NaturalJacquetDualityStatement
Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
Langlands.Representation.Parabolic.NormalizedCompatibilityStatement
Langlands.Representation.Parabolic.NormalizedInductionStatement
Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof
Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof
Langlands.Representation.Parabolic.NormalizedJacquetStatement
Langlands.Representation.Parabolic.OppositeJacquetAdmissibilityProof
Langlands.Representation.Parabolic.OppositeJacquetAdmissibilityStatement
Langlands.Representation.Parabolic.OppositeRefinementDefinitions
Langlands.Representation.Parabolic.OppositeRefinementFunctors
Langlands.Representation.Parabolic.OppositeRefinementTransitivityProof
Langlands.Representation.Parabolic.OppositeRefinementTransitivityStatement
Langlands.Representation.Parabolic.OrderedProductRegroupingEquivalence
Langlands.Representation.Parabolic.OrderedProductRegroupingProof
Langlands.Representation.Parabolic.OrderedProductRegroupingStatement
Langlands.Representation.Parabolic.ProductInductionSubrepresentation
Langlands.Representation.Parabolic.QuotientCompactProof
Langlands.Representation.Parabolic.RefinedInductionAdmissibility
Langlands.Representation.Parabolic.RefinedInductionTensorMap
Langlands.Representation.Parabolic.RefinedInductionTensorNormalization
Langlands.Representation.Parabolic.RefinedInductionTensorProof
Langlands.Representation.Parabolic.RefinedInductionTensorStatement
Langlands.Representation.Parabolic.RefinementCharacter
Langlands.Representation.Parabolic.RefinementComposition
Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationProof
Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement
Langlands.Representation.Parabolic.RefinementInductionTransitivityProof
Langlands.Representation.Parabolic.RefinementPreimage
Langlands.Representation.Parabolic.RefinementTransitivityStatement
Langlands.Representation.Parabolic.RegroupingFactorEquivalences
Langlands.Representation.Parabolic.SecondAdjointnessAssembly
Langlands.Representation.Parabolic.SecondAdjointnessProof
Langlands.Representation.Parabolic.SecondAdjointnessStatement
Langlands.Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof
Langlands.Representation.Parabolic.ThreeBlockCarrierComparison
Langlands.Representation.Parabolic.ThreeBlockInductionAssociativityStatement
Langlands.Representation.Parabolic.ThreeBlockRefinementGeometry
Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly
Langlands.Representation.Parabolic.ThreeBlockUniverseReduction
Langlands.Representation.Parabolic.UnipotentFiniteContainment
Langlands.Representation.RankinSelberg.AnalyticStatement
Langlands.Representation.RankinSelberg.EqualRankFrobeniusProof
Langlands.Representation.RankinSelberg.EqualRankFrobeniusStatement
Langlands.Representation.RankinSelberg.EqualRankTrilinearAssembly
Langlands.Representation.RankinSelberg.EqualRankTrilinearReduction
Langlands.Representation.RankinSelberg.EqualRankTrilinearUniquenessStatement
Langlands.Representation.RankinSelberg.FunctionalEquationStatement
Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
Langlands.Representation.RankinSelberg.HaarSymmetriesProof
Langlands.Representation.RankinSelberg.HaarSymmetriesStatement
Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement
Langlands.Representation.RankinSelberg.LocalFactor
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.QuotientIntegrals
Langlands.Representation.RankinSelberg.RankOneQuotient
Langlands.Representation.RankinSelberg.RationalContinuation
Langlands.Representation.RankinSelberg.RationalZeta
Langlands.Representation.RankinSelberg.TwistInvariance
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.RankinSelberg.UnipotentQuotient
Langlands.Representation.RankinSelberg.UnipotentUnimodularity
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement
Langlands.Representation.Schur.CountableDimensionProof
Langlands.Representation.Schur.CountableDimensionStatement
Langlands.Representation.Shahidi.Geometry
Langlands.Representation.Shahidi.Induction
Langlands.Representation.Shahidi.IntertwiningCovariance
Langlands.Representation.Shahidi.IntertwiningInduced
Langlands.Representation.Shahidi.IntertwiningIntegral
Langlands.Representation.Shahidi.TwoBlocks
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.EmbeddingProof
Langlands.Representation.Smooth.Admissibility.EmbeddingStatement
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Admissibility.ExactProof
Langlands.Representation.Smooth.Admissibility.ExactStatement
Langlands.Representation.Smooth.Admissibility.Extension
Langlands.Representation.Smooth.Admissibility.FiniteLengthProof
Langlands.Representation.Smooth.Admissibility.FiniteLengthStatement
Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
Langlands.Representation.Smooth.Contragredient.AdmissibleDualityStatement
Langlands.Representation.Smooth.Contragredient.CompactDualityProof
Langlands.Representation.Smooth.Contragredient.CompactDualityStatement
Langlands.Representation.Smooth.Contragredient.Definitions
Langlands.Representation.Smooth.Contragredient.ExactProof
Langlands.Representation.Smooth.Contragredient.ExactStatement
Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions
Langlands.Representation.Smooth.Contragredient.GelfandKazhdanAssembly
Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof
Langlands.Representation.Smooth.Contragredient.GelfandKazhdanStatement
Langlands.Representation.Smooth.Contragredient.HomDualityProof
Langlands.Representation.Smooth.Contragredient.HomDualityStatement
Langlands.Representation.Smooth.Contragredient.InvariantPairingProof
Langlands.Representation.Smooth.Contragredient.InvariantPairingStatement
Langlands.Representation.Smooth.Contragredient.LawsProof
Langlands.Representation.Smooth.Contragredient.LawsStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.Factorization.MultiplicityDefinitions
Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof
Langlands.Representation.Smooth.Factorization.TwoFactorStatement
Langlands.Representation.Smooth.FiniteLengthGrothendieck
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.FixedVectors.Detection
Langlands.Representation.Smooth.FixedVectors.FiniteTypes
Langlands.Representation.Smooth.FixedVectors.FiniteTypesStatement
Langlands.Representation.Smooth.FixedVectors.GenerationInheritance
Langlands.Representation.Smooth.FixedVectors.GenerationInheritanceStatement
Langlands.Representation.Smooth.FixedVectors.LawsProof
Langlands.Representation.Smooth.FixedVectors.LawsStatement
Langlands.Representation.Smooth.FixedVectors.OrderProof
Langlands.Representation.Smooth.FixedVectors.OrderStatement
Langlands.Representation.Smooth.Schur.Proof
Langlands.Representation.Smooth.Schur.Statement
Langlands.Representation.Smooth.SmallRealizationProof
Langlands.Representation.Smooth.SmallRealizationStatement
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions
Langlands.Representation.Smooth.Transfer.GroupEquivalence
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.SubrepresentationLattice
Langlands.Representation.Tensor.CoinvariantReflection
Langlands.Representation.Tensor.ExternalFiltration
Langlands.Representation.Tensor.ExternalSubquotient
Langlands.Representation.Tensor.ExternalSubrepresentation
Langlands.Representation.Tensor.FactorMatchingProof
Langlands.Representation.Tensor.FactorMatchingStatement
Langlands.Representation.Tensor.Filtration
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteEquivalences
Langlands.Representation.Tensor.FiniteFiltration
Langlands.Representation.Tensor.FiniteProperties
Langlands.Representation.Tensor.FiniteRegrouping
Langlands.Representation.Tensor.FlattenedGLRefinement
Langlands.Representation.Tensor.GLRefinement
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Tensor.ProductFiltration
Langlands.Representation.Tensor.SmoothDual
Langlands.Representation.Tensor.SmoothDualInjectivityProof
Langlands.Representation.Tensor.SmoothDualInjectivityStatement
Langlands.Representation.Tensor.SmoothDualSurjectivityProof
Langlands.Representation.Tensor.SmoothDualSurjectivityStatement
Langlands.Representation.Tensor.SmoothSubquotients
Langlands.Representation.Tensor.UnitaryProof
Langlands.Representation.Tensor.UnitaryStatement
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.DualProof
Langlands.Representation.Twist.DualStatement
Langlands.Representation.Twist.LeviComplexPower
Langlands.Representation.Twist.LeviRealPower
Langlands.Representation.Twist.PullbackProof
Langlands.Representation.Twist.PullbackStatement
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothPartDefinitions
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Unitary.Basic
Langlands.Representation.Unitary.CentralCharacterProof
Langlands.Representation.Unitary.CentralCharacterStatement
Langlands.Representation.Unitary.HermitianDual
Langlands.Representation.Unitary.LeviCuspidalRealUnitarizationProof
Langlands.Representation.Unitary.LeviCuspidalRealUnitarizationStatement
Langlands.Representation.Unitary.SquareIntegrableProof
Langlands.Representation.Unitary.SquareIntegrableStatement
Langlands.Representation.Unitary.SupercuspidalRealUnitarizationProof
Langlands.Representation.Unitary.SupercuspidalRealUnitarizationStatement
Langlands.Representation.Unitary.Twist
Langlands.Representation.Unitary.UnitarizabilityContinuationProof
Langlands.Representation.Unitary.UnitarizabilityContinuationStatement
Langlands.Representation.Unramified.Eigenvalues
Langlands.Representation.Unramified.HeckeOperators
Langlands.Representation.Unramified.PrincipalSeries
Langlands.Representation.Unramified.SphericalClassificationStatement
Langlands.Representation.Unramified.SphericalConstituentExistenceProof
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.AlgebraicTwist
Langlands.Representation.Whittaker.BruhatCellDistribution
Langlands.Representation.Whittaker.BruhatCellFactorizationProof
Langlands.Representation.Whittaker.BruhatCellFactorizationStatement
Langlands.Representation.Whittaker.BruhatCellInvarianceProof
Langlands.Representation.Whittaker.BruhatCellInvarianceStatement
Langlands.Representation.Whittaker.BruhatCellRestrictionVanishingProof
Langlands.Representation.Whittaker.BruhatCellRestrictionVanishingStatement
Langlands.Representation.Whittaker.BruhatCellVanishingProof
Langlands.Representation.Whittaker.BruhatCellVanishingStatement
Langlands.Representation.Whittaker.BruhatCompatibleSupportProof
Langlands.Representation.Whittaker.BruhatCompatibleSupportStatement
Langlands.Representation.Whittaker.BruhatFiberAverage
Langlands.Representation.Whittaker.BruhatFiberCharacterCovarianceProof
Langlands.Representation.Whittaker.BruhatFiberCharacterCovarianceStatement
Langlands.Representation.Whittaker.BruhatHaarMeasureProof
Langlands.Representation.Whittaker.BruhatHaarMeasureStatement
Langlands.Representation.Whittaker.BruhatOrbitalIntegrationProof
Langlands.Representation.Whittaker.BruhatOrbitalIntegrationStatement
Langlands.Representation.Whittaker.BundledDualTransport
Langlands.Representation.Whittaker.CharacterChange
Langlands.Representation.Whittaker.CoefficientDistribution
Langlands.Representation.Whittaker.CompatibleMonomialFixedProof
Langlands.Representation.Whittaker.CompatibleMonomialFixedStatement
Langlands.Representation.Whittaker.CompatibleTorus
Langlands.Representation.Whittaker.Distribution
Langlands.Representation.Whittaker.DistributionInvarianceProof
Langlands.Representation.Whittaker.DistributionInvarianceStatement
Langlands.Representation.Whittaker.DualTransform
Langlands.Representation.Whittaker.EntrywiseCharacter
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.GeneralizedCoefficient
Langlands.Representation.Whittaker.GeneralizedCoefficientDescent
Langlands.Representation.Whittaker.GeneralizedCoefficientKernelProof
Langlands.Representation.Whittaker.GeneralizedCoefficientKernelStatement
Langlands.Representation.Whittaker.GeneralizedCoefficientSeparation
Langlands.Representation.Whittaker.GenericDualTransport
Langlands.Representation.Whittaker.Iwasawa
Langlands.Representation.Whittaker.MirabolicQuotientMeasure
Langlands.Representation.Whittaker.MultiplicityOneProof
Langlands.Representation.Whittaker.MultiplicityOneStatement
Langlands.Representation.Whittaker.PrerequisiteInterfaces
Langlands.Representation.Whittaker.PrerequisitesStatement
Langlands.Representation.Whittaker.Twist
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.ConjugationStabilizer
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.GroupAction.FiniteOrbitProof
Langlands.Topology.GroupAction.FiniteOrbitStatement
Langlands.Topology.Nonarchimedean.Subgroup
Langlands.VirtualRepresentation.Exact
Langlands.VirtualRepresentation.ExactTwist
Langlands.VirtualRepresentation.Integral
Langlands.Weil.Algebraic
Langlands.Weil.AlgebraicProof
Langlands.Weil.Local.Assembly
Langlands.Weil.Local.DegreeCharacters
Langlands.Weil.Local.Parameters
Langlands.Weil.Local.ResidueCharacters
Langlands.Weil.Pullback
Langlands.Weil.Representation.Basic
Langlands.Weil.Representation.CharacterLine
Langlands.Weil.Representation.Continuity
Langlands.Weil.Representation.ContinuityProof
Langlands.Weil.Representation.Determinant
Langlands.Weil.Representation.DirectSum
Langlands.Weil.Representation.Dual
Langlands.Weil.Representation.DualClasses
Langlands.Weil.Representation.IsomorphismInvarianceProof
Langlands.Weil.Representation.OperationClosureProof
Langlands.Weil.Representation.Operations
Langlands.Weil.Representation.Predicates
Langlands.Weil.Representation.Twist
Langlands.Weil.Representation.TwistClasses
Langlands.Weil.Representation.TwistProperties
Langlands.Weil.Topology
Langlands.Weil.TopologyProof
Langlands.WeilDeligne.Basic
Langlands.WeilDeligne.DirectSum
Langlands.WeilDeligne.Dual
Langlands.WeilDeligne.ParameterRelations
Langlands.WeilDeligne.Parameters
Langlands.WeilDeligne.Twist
```

## Appendix: external import roots

These are the direct nonproject imports of the modules in the project closure, not a traversal of Mathlib or Lean internals.

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.Algebra.Bilinear
Mathlib.Algebra.Algebra.NonUnitalHom
Mathlib.Algebra.Algebra.NonUnitalSubalgebra
Mathlib.Algebra.Algebra.Subalgebra.Lattice
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Finprod
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.BigOperators.Group.List.Basic
Mathlib.Algebra.BigOperators.GroupWithZero.Action
Mathlib.Algebra.BigOperators.Pi
Mathlib.Algebra.Category.ModuleCat.Basic
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.DirectSum.Module
Mathlib.Algebra.Exact.Basic
Mathlib.Algebra.Field.Subfield.Basic
Mathlib.Algebra.Group.Action.Hom
Mathlib.Algebra.Group.Action.Opposite
Mathlib.Algebra.Group.AddChar
Mathlib.Algebra.Group.Equiv.TypeTags
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Group.Pi.Lemmas
Mathlib.Algebra.Group.Subgroup.Ker
Mathlib.Algebra.Group.Subgroup.Pointwise
Mathlib.Algebra.Group.Submonoid.Basic
Mathlib.Algebra.Group.TypeTags.Finite
Mathlib.Algebra.Group.TypeTags.Hom
Mathlib.Algebra.Module.CharacterModule
Mathlib.Algebra.Module.LinearMap.FiniteRange
Mathlib.Algebra.Module.Opposite
Mathlib.Algebra.Module.PID
Mathlib.Algebra.Module.Projective
Mathlib.Algebra.Module.Submodule.Map
Mathlib.Algebra.Module.ULift
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Order.BigOperators.Group.Finset
Mathlib.Algebra.Polynomial.FieldDivision
Mathlib.Algebra.Polynomial.Laurent
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Algebra.Polynomial.Module.AEval
Mathlib.Algebra.Polynomial.Module.FiniteDimensional
Mathlib.Algebra.Polynomial.Roots
Mathlib.Algebra.Ring.GeomSum
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Cardinality
Mathlib.Analysis.Complex.Circle
Mathlib.Analysis.Complex.Polynomial.Basic
Mathlib.Analysis.Fourier.FourierTransform
Mathlib.Analysis.InnerProductSpace.Defs
Mathlib.Analysis.InnerProductSpace.Dual
Mathlib.Analysis.InnerProductSpace.TensorProduct
Mathlib.Analysis.Matrix.Hermitian
Mathlib.Analysis.Matrix.MeasurableSpace
Mathlib.Analysis.Matrix.Normed
Mathlib.Analysis.MeanInequalitiesPow
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Complex.Circle
Mathlib.Analysis.SpecialFunctions.Log.Base
Mathlib.Analysis.SpecialFunctions.Pow.Complex
Mathlib.Analysis.SpecialFunctions.Pow.Continuity
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Analysis.SpecialFunctions.Sqrt
Mathlib.Analysis.SpecificLimits.Basic
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.Abelian.Subcategory
Mathlib.CategoryTheory.Discrete.Basic
Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
Mathlib.CategoryTheory.Products.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.CategoryTheory.Whiskering
Mathlib.Combinatorics.Enumerative.Composition
Mathlib.Data.ENat.Basic
Mathlib.Data.ENat.BigOperators
Mathlib.Data.Fin.Rev
Mathlib.Data.Fin.Tuple.Basic
Mathlib.Data.Fin.Tuple.Sort
Mathlib.Data.Finset.NatAntidiagonal
Mathlib.Data.Fintype.EquivFin
Mathlib.Data.Fintype.Quotient
Mathlib.Data.Fintype.Sort
Mathlib.Data.Fintype.Sum
Mathlib.Data.Int.Cast.Lemmas
Mathlib.Data.Int.Interval
Mathlib.Data.Int.LeastGreatest
Mathlib.Data.List.Pairwise
Mathlib.Data.Matrix.Basic
Mathlib.Data.Matrix.Block
Mathlib.Data.Nat.Find
Mathlib.Data.PNat.Basic
Mathlib.Data.Set.Card
Mathlib.Data.Set.Finite.Basic
Mathlib.Data.Sym.Basic
Mathlib.Data.ZMod.Basic
Mathlib.FieldTheory.AbsoluteGaloisGroup
Mathlib.FieldTheory.Finite.Basic
Mathlib.FieldTheory.Finite.Extension
Mathlib.FieldTheory.Galois.Profinite
Mathlib.FieldTheory.PrimitiveElement
Mathlib.FieldTheory.RatFunc.AsPolynomial
Mathlib.GroupTheory.Abelianization.Defs
Mathlib.GroupTheory.Coset.Defs
Mathlib.GroupTheory.DoubleCoset
Mathlib.GroupTheory.FiniteIndexNormalSubgroup
Mathlib.GroupTheory.GroupAction.Basic
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.GroupTheory.GroupAction.Defs
Mathlib.GroupTheory.GroupAction.Quotient
Mathlib.GroupTheory.Index
Mathlib.GroupTheory.OrderOfElement
Mathlib.GroupTheory.QuotientGroup.Defs
Mathlib.GroupTheory.Subgroup.Center
Mathlib.GroupTheory.Subgroup.Centralizer
Mathlib.GroupTheory.Transfer
Mathlib.LinearAlgebra.AffineSpace.AffineMap
Mathlib.LinearAlgebra.AnnihilatingPolynomial
Mathlib.LinearAlgebra.Basis.VectorSpace
Mathlib.LinearAlgebra.BilinearForm.Properties
Mathlib.LinearAlgebra.BilinearMap
Mathlib.LinearAlgebra.Charpoly.Basic
Mathlib.LinearAlgebra.Charpoly.ToMatrix
Mathlib.LinearAlgebra.Determinant
Mathlib.LinearAlgebra.Dimension.Basic
Mathlib.LinearAlgebra.Dimension.Constructions
Mathlib.LinearAlgebra.Dimension.StrongRankCondition
Mathlib.LinearAlgebra.DirectSum.Finite
Mathlib.LinearAlgebra.Dual.Defs
Mathlib.LinearAlgebra.Dual.Lemmas
Mathlib.LinearAlgebra.Eigenspace.Basic
Mathlib.LinearAlgebra.Eigenspace.Pi
Mathlib.LinearAlgebra.Eigenspace.Triangularizable
Mathlib.LinearAlgebra.FiniteDimensional.Basic
Mathlib.LinearAlgebra.FiniteDimensional.Defs
Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
Mathlib.LinearAlgebra.Finsupp.LinearCombination
Mathlib.LinearAlgebra.Finsupp.VectorSpace
Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
Mathlib.LinearAlgebra.Isomorphisms
Mathlib.LinearAlgebra.Matrix.BilinearForm
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
Mathlib.LinearAlgebra.Matrix.Diagonal
Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
Mathlib.LinearAlgebra.Matrix.Kronecker
Mathlib.LinearAlgebra.Matrix.NonsingularInverse
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.PosDef
Mathlib.LinearAlgebra.Matrix.Rank
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.Matrix.SchurComplement
Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
Mathlib.LinearAlgebra.Matrix.Transvection
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.LinearAlgebra.PiTensorProduct.Basis
Mathlib.LinearAlgebra.PiTensorProduct.Dual
Mathlib.LinearAlgebra.PiTensorProduct.Finite
Mathlib.LinearAlgebra.PiTensorProduct.Generators
Mathlib.LinearAlgebra.Projection
Mathlib.LinearAlgebra.Quotient.Basic
Mathlib.LinearAlgebra.Semisimple
Mathlib.LinearAlgebra.TensorProduct.Basis
Mathlib.LinearAlgebra.TensorProduct.Finiteness
Mathlib.LinearAlgebra.TensorProduct.RightExactness
Mathlib.LinearAlgebra.Trace
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
Mathlib.MeasureTheory.Constructions.Pi
Mathlib.MeasureTheory.Function.L2Space
Mathlib.MeasureTheory.Function.LocallyIntegrable
Mathlib.MeasureTheory.Function.LpSeminorm.Defs
Mathlib.MeasureTheory.Function.LpSpace.Indicator
Mathlib.MeasureTheory.Function.SimpleFunc
Mathlib.MeasureTheory.Group.Integral
Mathlib.MeasureTheory.Group.LIntegral
Mathlib.MeasureTheory.Group.MeasurableEquiv
Mathlib.MeasureTheory.Group.Measure
Mathlib.MeasureTheory.Group.ModularCharacter
Mathlib.MeasureTheory.Integral.Bochner.Basic
Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Integral.Marginal
Mathlib.MeasureTheory.Integral.Prod
Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.MeasureTheory.Measure.Haar.DistribChar
Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
Mathlib.MeasureTheory.Measure.Haar.Unique
Mathlib.MeasureTheory.Measure.Lebesgue.Basic
Mathlib.MeasureTheory.Measure.OpenPos
Mathlib.MeasureTheory.Measure.Prod
Mathlib.MeasureTheory.Measure.Regular
Mathlib.MeasureTheory.Measure.Typeclasses.Finite
Mathlib.NumberTheory.LocalField.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Atoms
Mathlib.Order.CompactlyGenerated.Basic
Mathlib.Order.Hom.Set
Mathlib.Order.Interval.Finset.Fin
Mathlib.Order.Interval.Set.Infinite
Mathlib.Order.WithBot
Mathlib.RepresentationTheory.Basic
Mathlib.RepresentationTheory.Coinduced
Mathlib.RepresentationTheory.Coinvariants
Mathlib.RepresentationTheory.Equiv
Mathlib.RepresentationTheory.Intertwining
Mathlib.RepresentationTheory.Invariants
Mathlib.RepresentationTheory.Irreducible
Mathlib.RepresentationTheory.Rep.Basic
Mathlib.RepresentationTheory.Rep.Res
Mathlib.RepresentationTheory.Semisimple
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.Adjoin.Basic
Mathlib.RingTheory.Adjoin.Polynomial.Basic
Mathlib.RingTheory.AdjoinRoot
Mathlib.RingTheory.Algebraic.LinearIndependent
Mathlib.RingTheory.Artinian.Module
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.Finiteness.Basic
Mathlib.RingTheory.Finiteness.Finsupp
Mathlib.RingTheory.Flat.Basic
Mathlib.RingTheory.FractionalIdeal.Operations
Mathlib.RingTheory.Ideal.Quotient.Basic
Mathlib.RingTheory.Ideal.Quotient.Operations
Mathlib.RingTheory.Jacobson.Semiprimary
Mathlib.RingTheory.Length
Mathlib.RingTheory.Localization.Ideal
Mathlib.RingTheory.Nakayama
Mathlib.RingTheory.Nilpotent.Basic
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.Norm.Transitivity
Mathlib.RingTheory.Polynomial.Basic
Mathlib.RingTheory.Polynomial.UniqueFactorization
Mathlib.RingTheory.PowerBasis
Mathlib.RingTheory.PrincipalIdealDomain
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.SimpleModule.Basic
Mathlib.RingTheory.SimpleModule.Rank
Mathlib.RingTheory.Trace.Basic
Mathlib.RingTheory.Valuation.Extension
Mathlib.RingTheory.Valuation.Integral
Mathlib.RingTheory.Valuation.LocalSubring
Mathlib.RingTheory.Valuation.RamificationGroup
Mathlib.Tactic
Mathlib.Tactic.Group
Mathlib.Tactic.Linarith
Mathlib.Tactic.LinearCombination
Mathlib.Tactic.NoncommRing
Mathlib.Tactic.NormNum
Mathlib.Tactic.Ring
Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
Mathlib.Topology.Algebra.ClopenNhdofOne
Mathlib.Topology.Algebra.ConstMulAction
Mathlib.Topology.Algebra.Constructions
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Field
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.ClosedSubgroup
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Neighborhood
Mathlib.Topology.Algebra.Group.OpenMapping
Mathlib.Topology.Algebra.Group.Pointwise
Mathlib.Topology.Algebra.Group.Quotient
Mathlib.Topology.Algebra.Group.Subgroup
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.GroupWithZero
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.Module.ModuleTopology
Mathlib.Topology.Algebra.MulAction
Mathlib.Topology.Algebra.MvPolynomial
Mathlib.Topology.Algebra.Nonarchimedean.Basic
Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.ProperAction.Basic
Mathlib.Topology.Algebra.Ring.Compact
Mathlib.Topology.Algebra.Ring.Ideal
Mathlib.Topology.Algebra.Support
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Baire.Lemmas
Mathlib.Topology.Baire.LocallyCompactRegular
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Compactness.LocallyCompact
Mathlib.Topology.Compactness.SigmaCompact
Mathlib.Topology.Connected.Clopen
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.ContinuousMap.CompactlySupported
Mathlib.Topology.Homeomorph.Defs
Mathlib.Topology.Homeomorph.Lemmas
Mathlib.Topology.Homeomorph.Quotient
Mathlib.Topology.Instances.Int
Mathlib.Topology.Instances.Matrix
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.Instances.Real.Lemmas
Mathlib.Topology.LocallyClosed
Mathlib.Topology.LocallyConstant.Algebra
Mathlib.Topology.LocallyConstant.Basic
Mathlib.Topology.MetricSpace.ProperSpace
Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
Mathlib.Topology.Order.Compact
Mathlib.Topology.Separation.Profinite
Mathlib.Topology.Sequences
Mathlib.Topology.UrysohnsLemma
```
