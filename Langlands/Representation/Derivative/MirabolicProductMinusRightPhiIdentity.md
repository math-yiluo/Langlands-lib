# The identity orbit piece of the right `Φ⁻` sequence

Author: Worker 837.

This module belongs to the proof of the clause
`Langlands.Derivative.MirabolicProductMinus.RightPhiShortExact.{uF,uV} F T` of the
published statement module
`Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`
(host task `6cd54f76-f453-4faa-818a-5843e1bbcaff`). Its entry theorem is

```lean
theorem Langlands.Derivative.MirabolicProductMinus.rightPhiIdentityPiece_iso
    (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k r : ℕ) :
    Nonempty (rightPhiPiece.{uF, uV} T ψ k r (rightRepresentative k r F.Carrier 1) ≅
      rightPhiQuotient.{uF, uV} T k (r + 1) ⋙ SmoothRep.toRep)
```

for every prime `p`, `F : PadicField.{uF} p`, `T`, `ψ`, `k` and `r`, with
independent universes `uF`, `uV`. It is the isomorphism `E₁` required by
`rightPhiShortExact_of_pieces` (`MirabolicProductMinusRightPhiAssembly`): the
normalized localized orbit piece of `τ × ρ` at the identity representative
is `(Ψ⁻τ) × (ρ|P_(k+1))`, naturally in `τ` on `P_(r+2)` and `ρ` on `GL_(k+1)`.
The cyclic piece `E₀` and the final clause are separate obligations; this unit
proves neither.

## Original and derived provenance

The original is BZ77, I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, registered as `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`:

- §1.8, printed pp.444–445 (PDF pp.5–6): normalized induction;
- §§3.1–3.2, printed pp.450–451 (PDF pp.11–12): the minus functors
  `Φ⁻ = r_{V,θ}` and `Ψ⁻`;
- §4.12, printed pp.456–458 (PDF pp.17–19): the mixed products, cases (II)
  and (III);
- Proposition 4.13(c), printed p.458 (PDF p.19): the exact sequence
  `0 → Φ⁻(τ) × ρ → Φ⁻(τ × ρ) → Ψ⁻(τ) × (ρ|P_k) → 0`;
- §7.2, printed p.471 (PDF p.32): the proof by the geometric lemma on two
  orbits of `P_(n-1) V_n`, details left to the reader.

The quotient term of 4.13(c) is the contribution of the identity orbit. The
route and all declarations of this module and its three helper modules are
derived internal content. The geometric lemma enters only through the
published Mackey sequence of `MirabolicPhiMinusMackey`, and the localization of
the orbit piece is computed with the published
`Induction.SplitStagesCharacter.comparisonEquiv`.

## The chain at an object

Let `t = k+r+1`, `Q = plusSubgroup t`, `P = rightStages k r 1`,
`S = rightIdStabilizer k r` and `K = P.comap plusSuccessor`
(`MirabolicProductMinusRightPhiIdentityGroups`). For `X = (τ, ρ)` the
equivalence `E X` is the composite of

1. `rightIdentityLocalizationEquiv₀`: the identity from `plusPhiLocalization`
   of the orbit piece to the published split-kernel `localizedAction`
   (`plusProjection`, `plusSuccessor`, `plusKernelThetaSmooth`) of the orbit
   piece;
2. `localizedActionEquiv` of `rightIdentityOrbitEquiv`: the orbit piece is
   compact induction from `S` of `rightIdentityCoefficient T k r τ ρ`
   (`χ_R (τ ⊠ ρ)` through the stabilizer), through the identity on vectors
   (`rightIdentityCoefficientBridge`, `compactInducedEquiv`);
3. the published `comparisonEquiv` at these data, to compact induction from
   `K` of the localized coefficient twisted by the Haar character;
4. under the `Φ⁻` twist `phiMinusCharacter T t`, the published
   `compactInductionTwistEquiv` moving the twist into the coefficient;
5. `rightIdentityCompactEquivOf`: the published `compactInducedTransport`
   along `rightIdentityCast` (the rank cast `P_(k+r+2) ≅ P_((r+1)+k+1)`, which
   carries `K` onto `leftSubgroup (r+1) k` by `mem_rightStages_one_comap_iff`)
   with `rightIdentityCoefficientEquiv`, followed by `compEquivOfEq` and
   `rightIdentityCast_toMonoidHom` to the pullback along the published
   `mirabolicCastHom (Nat.add_comm (r+1) k)`.

The transport hypothesis `hE` is the coefficient action: by
`coefficientAction_mk`, `rightIdentityCoefficientEquiv_section`,
`rightIdentity_psiMinus_tmul` and `rightIdentity_scalar_eq`, `l ∈ K` acts on the
coefficient by `χ_L(l) (Ψ⁻τ(A) ⊗ ρ(D))`, the normalized lower left mixed
coefficient of `(Ψ⁻τ, ρ|P)`. The character `η` of the kernel intersection is
trivial by `thetaPlus_rightStabilizer_one`.

The comparison data are proved here: closedness and containments from the
groups module; `ker plusProjection` closed; `plusSubgroup_compactOpenBasis`
(from `Langlands.subgroupNonarchimedean` and the published compact open basis
theorem); local compactness, Borel structures, the kernel basis and cover
transported from the radical `V_(t+2)` along
`splitStagesKernelContinuousEquiv` and `plusKernelContinuousEquiv`
(`compactOpenBasis_of_continuousMulEquiv`, published `radical_compactOpenBasis`);
Haar measures, unimodularity from the published
`Haar.compactOpenCoverUnimodularity`, and a compatible quotient measure from
`QuotientIntegration.compatibleMeasureExists`. The coefficient is smooth
(published `isSmooth_comp`, `isSmooth_twist_iff`,
`isSmooth_rightInducingRepresentation`).

## Naturality and the isomorphism

For a morphism `φ = (f₁, f₂)`, `chain_natural₅` combines: the identity step
(classes go to classes); `localizedActionEquiv_natural`; the published
`comparisonEquiv_natural`; the published `compactInductionTwistEquiv_natural`;
and `rightIdentityCompactEquivOf_natural`, whose coefficient condition is
`rightIdentityCoefficientEquiv_natural` on the class map of
`χ_R (f₁ ⊠ f₂)`. `NatIso.ofComponents` with `Rep.mkIso` gives
`rightPhiPiece … ≅ rightIdentityTarget T k r ⋙ toRep`, and the published
`mirabolicRankCastIso` replaces the explicit pullback by the actual
`mirabolicRankCast T (Nat.add_comm (r+1) k)` of `rightPhiQuotient T k (r+1)`.
The theorem uses `set_option maxHeartbeats 8000000`; it is a long proof whose
steps are each elementary.

## Generic and auxiliary declarations of this module

- `localizedActionEquiv r s θ hθ f`, `_mk`, `_natural`: an equivalence of
  representations induces an equivalence of the published localized section
  actions (published `Jacquet.Localization.representationEquiv`), natural for
  compatible intertwiners.
- `plusSubgroup_compactOpenBasis`, `rightIdentityCast`,
  `rightIdentityCast_toMonoidHom`, `rightIdentityTarget` (the target with the
  explicit pullback), `rightIdentityCompactEquivOf` and its `_natural`,
  `rightIdentityOrbitCoefficient`, `rightIdentityCoefficientBridge`,
  `rightIdentityLocalizationEquiv₀`, `rightIdentityOrbitEquiv`, `chain_natural₅`.

The stabilizer is used in the presentation of the orbit pieces
(`mirabolic (k+r+1+1)`); the published lemmas stated for `mirabolic (k+r+2)`
are applied to it unchanged. The coefficient of the orbit piece is first
identified with `rightIdentityCoefficient` by the identity map at the top
level, which keeps elaboration small.

## Mathematical dependency and restriction audit

This unit consists of this module and the three helper modules
`MirabolicProductMinusRightPhiAssembly`, `MirabolicProductMinusRightPhiIdentityGroups`
and `MirabolicProductMinusRightPhiIdentityCoefficient`, each with its own
Markdown. All other inputs are independently accepted and published. No
Library module is modified. Proposition definitions in the closure supply types
and constructions; none is used as a proof of its conclusion.

| Condition | Actual dependency and scope |
| --- | --- |
| Localized compact induction | The published `SplitStagesCharacter.comparisonEquiv`, `coefficientAction_mk` and `comparisonEquiv_natural` (proof of the published `SplitStagesCharacterComparisonStatement`) are used with the actual groups, character and coefficient. All their hypotheses are proved in this unit. No comparison or bijectivity premise is assumed. |
| Mackey sequence | `MirabolicPhiMinusMackey` (published) supplies `plusPhiLocalization` and, in the assembly helper, the localized two-orbit sequence. No orbit enumeration is proved or assumed in this unit; the assembly takes the enumeration as a hypothesis. The published orbit-coverage proof is not imported. |
| Orbit data | `MirabolicMixedOrbitData`, `MirabolicMixedOrbitStages`, `MirabolicMixedOrbitSections` and `MirabolicMixedOrbitSectionCoefficients` (published) supply the representatives, stabilizers, sections and coefficient formulas. |
| Haar ratio and normalization | The ratio `|det D|` is computed from the published `mulEquivHaarChar_conj_levi_inv` and kernel identifications. The `Φ⁻`, `Ψ⁻`, case (II) and case (III) normalizations are the actual published characters, and the real-power identity is proved (published `rightPsi_scalar_identity_complex`). No residual twist is assumed. |
| Coefficient tensor quotient | The identification uses the published `rightPsiTensorEquiv` and quotient universal properties. No finiteness conclusion is used. |
| Right Psi and right boundary modules | `MirabolicProductMinusRightPsi`, `…RightPsiGroups`, `…RightPsiCoefficient` and `…RightBoundary` (published) supply lower lemmas (compact open bases, `compEquivOfEq`, `compactInductionTwistEquiv_natural`, `rightPsiKernel`, `rightPsiTensorEquiv`, `mirabolicCastHom`, `mirabolicRankCastIso`, radical bases, Haar moduli). Their clause theorems `rightPsiCompatibility` and `rightPhiBoundary` are not used. |
| Restriction-sequence modules | `MirabolicProductRestrictionTransport` supplies only `compactInducedTransport`; `MirabolicProductRestrictionMackey` (through the Mackey module) supplies only `RepFunctorFiltration.exists_exact_of_two`. No BZ77 4.13(a) conclusion is used. |
| Unimodularity and quotient measures | `Haar.compactOpenCoverUnimodularity` and `QuotientIntegration.compatibleMeasureExists` are measure-theoretic results on locally compact groups. |
| Plus functors and adjunction | From `MirabolicPlus` only the character `thetaPlus` and its laws are used. `Induction.StructuralStatement` (through `CharacterTwistProof`) supplies only proposition definitions, including `OpenSubgroupAdjunctionClause`; none is used as a proof. |
| BZ77 4.13(d) and general Leibniz | No submodule-detection conclusion, general Leibniz proof or derivative-filtration theorem is used. `Filtration.Definitions` supplies definitions only. |
| Segment derivative and Jacquet formulas | No segment derivative formula, Ze80 §3.5 or §9.6, `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula` or `SegmentSpecialJacquetExponentNormFormula` supplies a direct or transitive input. |
| Individual segment existence | No individual special-head/reverse-socle or segment-socle/reverse-head existence conclusion, proof successor or downstream consequence is used. |
| Linked and unlinked socle consumers | `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`, `JuxtaposedSegmentSocleReverseProductStructure` and `LinkedSegmentSocleReverseProductQuotientHom` are absent from the dependencies. |
| Segment product and commutation consumers | No `SegmentSocleProductIrreducibility`, `AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`, `LinkedSegmentSocleGluing`, Ze80 4.2 or 9.7 criterion, or their successors or consequences is used. |
| Special-head criterion and uniqueness | `SegmentHeadProductIrreducibility` and `GenericSegmentProductUniqueness`, their parent tasks, successors and downstream consequences supply no input. |
| Ordered existence and multisegment exhaustion | No `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`, ordered strong-head existence, special-head multisegment exhaustion, quotient coverage or ordered-conversion conclusion is used. |
| Analytic, tempered and square-integrable classification | No analytic segment classification, `SegmentSpecialEssentialSquareIntegrability`, tempered uniqueness, `SquareIntegrableLanglandsClassification`, square-integrable or regular exhaustion, or Ze80 9.3 conclusion is used, including their successors and consequences. |
| Two-supercuspidal consumers | Neither `TwoSupercuspidalNonadjacentProductIrreducible` nor `TwoSupercuspidalProductStructure`, their full-product assembly, successors or consequences is imported or used. |
| Supercuspidal and single-block finiteness | No `SupercuspidalCoinvariantFinitenessStatement`, all-character single-block conclusion or downstream consequence supplies an input. No arbitrary-character finiteness theorem is used. |
| Other Whittaker finiteness exclusions | `IrreducibleCoinvariantFinitenessStatement` and `LeviCuspidalCoinvariantFinitenessStatement`, their parent and proof tasks and their consequences are absent, as is the prohibited mirabolic finite-length route. |
| Whittaker and Rankin–Selberg modules in the closure | They provide character, coefficient, measure, compact-orbit, cutoff and unimodularity constructions brought by the generic induction infrastructure, and supply no excluded input. |
| Host clauses and pending results | The compatibility statement module supplies only the unchanged proposition and functor definitions. No host clause theorem is used. No left `Φ⁻` comparison, cyclic orbit piece, pending candidate, draft or consumer conclusion is imported or used. |
| Parameters and run controls | `T`, `ψ`, `k`, `r` and all smooth input carriers, including zero objects, are arbitrary. No suspended or paused worker supplies or waives an obligation. |

These rows cover every named task in the host's inherited exclusion union, its
mathematical conclusions, proof successors and downstream consequences. A
search over the source of the complete closure below and of this module found
no excluded declaration name and no task identifier in Lean code; the only
match of `admit` is English text in a docstring of
`Geometric.ClosedSubgroupStatement`. The search found no `sorry`, `native_decide`
or new axiom. The entry theorem depends only on `propext`, `Classical.choice`
and `Quot.sound`.

## Complete project import closure

There are exactly 246 transitive project imports, excluding this module, at
Library base `fe1d50ac5fc58387b768e0341e76ab0f3146bf25`, computed from the
actual import lines. Three of them are the helper modules of this unit; every
other entry is published and its Lean/Markdown pair is byte-identical to that
commit. Mathlib dependencies come from the pinned Lean environment.

```text
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
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockDeterminant
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.CompactOpen
Langlands.Group.GL.CountabilityProof
Langlands.Group.GL.CountabilityStatement
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedOrbitData
Langlands.Group.GL.MirabolicMixedOrbitSectionCoefficients
Langlands.Group.GL.MirabolicMixedOrbitSections
Langlands.Group.GL.MirabolicMixedOrbitStages
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicModularCharacterProof
Langlands.Group.GL.MirabolicModularCharacterStatement
Langlands.Group.GL.MirabolicModulusProof
Langlands.Group.GL.MirabolicModulusStatement
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.PadicOppositeBlocks
Langlands.Group.GL.PadicUpperUnipotent
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.ReverseBlocks
Langlands.Group.GL.TriangularParabolic
Langlands.Group.GL.UpperUnipotent
Langlands.Group.GL.UpperUnipotentCompactContainmentProof
Langlands.Group.GL.UpperUnipotentCompactContainmentStatement
Langlands.Group.HaarModulus
Langlands.HarmonicAnalysis.AlgebraicIntegral
Langlands.HarmonicAnalysis.AlgebraicIntegrand
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.Conductor
Langlands.HarmonicAnalysis.HaarConjugacy
Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicLatticeTopology
Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.LocalFactor.Harmonic.Statement
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalContragredientAux
Langlands.Representation.Classification.SupercuspidalContragredientStatement
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.OrbitMeanTranslation
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Compact.SurjectivityProof
Langlands.Representation.Compact.SurjectivityStatement
Langlands.Representation.Conductor.Congruence
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMinusExactnessProof
Langlands.Representation.Derivative.MirabolicMinusExactnessStatement
Langlands.Representation.Derivative.MirabolicPhiMinusMackey
Langlands.Representation.Derivative.MirabolicPlus
Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiAssembly
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityGroups
Langlands.Representation.Derivative.MirabolicProductMinusRightPsi
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiGroups
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiZero
Langlands.Representation.Derivative.MirabolicProductRestrictionFactors
Langlands.Representation.Derivative.MirabolicProductRestrictionMackey
Langlands.Representation.Derivative.MirabolicProductRestrictionOrbits
Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
Langlands.Representation.Dual.Definitions
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.QuotientFirstIso
Langlands.Representation.Geometric.ClosedSubgroupAssembly
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
Langlands.Representation.Geometric.ClosedSubgroupMackeyProof
Langlands.Representation.Geometric.ClosedSubgroupStatement
Langlands.Representation.Geometric.CompactOrbitRestriction
Langlands.Representation.Geometric.CosetAction
Langlands.Representation.Geometric.CosetOrbitHomeomorph
Langlands.Representation.Geometric.OrbitRestriction
Langlands.Representation.Geometric.OrbitSectionExtensionProof
Langlands.Representation.Geometric.OrbitSectionExtensionStatement
Langlands.Representation.Induction.BinaryPositiveCompact
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.CharacterTwistProof
Langlands.Representation.Induction.CompactAutomorphism
Langlands.Representation.Induction.CompactAutomorphismIntegralProof
Langlands.Representation.Induction.CompactAutomorphismIntegralStatement
Langlands.Representation.Induction.CompactCoinvariantBijectivityProof
Langlands.Representation.Induction.CompactCoinvariantBijectivityStatement
Langlands.Representation.Induction.CompactCoinvariantIntegral
Langlands.Representation.Induction.CompactCoinvariantLocalInverseProof
Langlands.Representation.Induction.CompactCoinvariantLocalInverseStatement
Langlands.Representation.Induction.CompactLocalSection
Langlands.Representation.Induction.CompactLocalSectionSpanningProof
Langlands.Representation.Induction.CompactLocalSectionSpanningStatement
Langlands.Representation.Induction.CompactLocallyConstant
Langlands.Representation.Induction.CompactQuotientCutoff
Langlands.Representation.Induction.CompactQuotientProof
Langlands.Representation.Induction.CompactSurjectivityProof
Langlands.Representation.Induction.CompactSurjectivityStatement
Langlands.Representation.Induction.CompactTransitivityProof
Langlands.Representation.Induction.CompactTransitivityStatement
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.InverseTranspose
Langlands.Representation.Induction.NormalCoinvariantKernelProof
Langlands.Representation.Induction.NormalCoinvariantKernelStatement
Langlands.Representation.Induction.NormalCoinvariantMap
Langlands.Representation.Induction.NormalCoinvariantProof
Langlands.Representation.Induction.NormalCoinvariantStatement
Langlands.Representation.Induction.NormalSplitComparison
Langlands.Representation.Induction.OppositeParabolic
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.SplitKernelCharacter
Langlands.Representation.Induction.SplitKernelCharacterExtension
Langlands.Representation.Induction.SplitKernelCompact
Langlands.Representation.Induction.SplitKernelCovariance
Langlands.Representation.Induction.SplitKernelEquivariant
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
Langlands.Representation.Jacquet.CharacterAveraging
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.ExactProof
Langlands.Representation.Jacquet.ExactStatement
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.LocalizationExactnessProof
Langlands.Representation.Jacquet.LocalizationExactnessStatement
Langlands.Representation.Jacquet.LocalizationTransport
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Mirabolic.LeftMixedProductSuccessor
Langlands.Representation.Mirabolic.MixedProducts
Langlands.Representation.OrbitSpan
Langlands.Representation.Parabolic.GeometricPrerequisitesStatement
Langlands.Representation.Parabolic.QuotientCompactProof
Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.QuotientIntegrals
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.RankinSelberg.UnipotentUnimodularity
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Contragredient.CompactDualityProof
Langlands.Representation.Smooth.Contragredient.CompactDualityStatement
Langlands.Representation.Smooth.Contragredient.Definitions
Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions
Langlands.Representation.Smooth.Contragredient.LawsProof
Langlands.Representation.Smooth.Contragredient.LawsStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.SmallRealizationProof
Langlands.Representation.Smooth.SmallRealizationStatement
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteEquivalences
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Unitary.Basic
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.Iwasawa
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.ConjugationStabilizer
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.Nonarchimedean.Subgroup
```
