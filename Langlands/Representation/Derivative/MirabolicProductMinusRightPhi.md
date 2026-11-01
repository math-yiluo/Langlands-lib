# The positive-rank `Φ⁻` sequence of BZ77 Proposition 4.13(c)

Author: Worker 837.

This module proves the clause
`Langlands.Derivative.MirabolicProductMinus.RightPhiShortExact.{uF,uV} F T` of the
published statement module
`Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`
(host task `6cd54f76-f453-4faa-818a-5843e1bbcaff`, component 5). Its theorem is

```lean
theorem Langlands.Derivative.MirabolicProductMinus.rightPhiShortExact
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) :
    RightPhiShortExact.{uF, uV} F T
```

with independent universes `uF`, `uV` and no further hypothesis. Unfolded: for
every `ψ` and `k r : ℕ` there are natural transformations
`i : rightPhiSubobject T ψ k r ⟶ rightPhiProduct T ψ k (r+1)` and
`q : rightPhiProduct T ψ k (r+1) ⟶ rightPhiQuotient T k (r+1)` such that at every
pair `X = (τ, ρ)`, with `τ` on `P_(r+2)` (`mirabolic (r+1)`) and `ρ` on
`GL_(k+1)`, the component of `i` is injective, its range is the kernel of the
component of `q`, and the component of `q` is surjective. This is

```text
0 → (Φ⁻τ) × ρ → Φ⁻(τ × ρ) → (Ψ⁻τ) × (ρ|P_(k+1)) → 0
```

for source `P_m`, `m = r+2 ≥ 2`, and GL rank `K = k+1`, with the published
functors: `rightPhiSubobject` is `(phiMinus T ψ r, 𝟭)` followed by the right mixed
product `T.rightMixedProductFunctor (k+1) r` and `mirabolicRankCast (Nat.succ_add k r)`
to `P_(k+r+2)`; `rightPhiProduct T ψ k (r+1)` is `phiMinus T ψ (k+(r+1))` applied to the
right mixed product of shape `(k+1, r+1)` transported by
`mirabolicRankCast (Nat.succ_add k (r+1))` to `P_(k+r+3)`; `rightPhiQuotient`
is `(psiMinus T (r+1), generalLinearRestriction T k)` followed by the left mixed
product `T.leftMixedProductFunctor (r+1) k` and
`mirabolicRankCast (Nat.add_comm (r+1) k)`. The normalizations are the published
inverse-half determinant characters of `Φ⁻` and `Ψ⁻` and the published mixed
characters, including the case (III) factor; arbitrary smooth inputs, including
zero objects, are retained.

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
- §7.2, printed p.471 (PDF p.32): the proof by restriction to `P_(n-1) V_n`,
  the geometric lemma on its two orbits (the open one giving the subobject,
  the closed one the quotient) and localization, with details left to the
  reader.

The implemented route follows §7.2. The orbit calculations, the
Haar ratios, the coefficient identifications and the scalar identities are
derived internal content of this unit and of the published identity-orbit
unit.

## The implemented proof

`rightPhiShortExact` fixes `ψ, k, r`, takes the ordered enumeration `s` of the two
`(H, Q)` double cosets, `H = rightInducing k r`, `Q = plusSubgroup (k+r+1)`, with
`s.representative = rightRepresentative k r` (cycle first) from the second
conjunct of the published theorem `mirabolicMixedOrbitCoverage`
(`MirabolicMixedOrbitCoverageProof`, proving the published
`MirabolicMixedOrbitCoverageStatement`), and applies the published
`rightPhiShortExact_of_pieces` (`MirabolicProductMinusRightPhiAssembly`) to `s`
and the two orbit-piece isomorphisms:

- `E₀ = rightPhiCyclePiece_iso T ψ k r` (this unit,
  `MirabolicProductMinusRightPhiCycle`): the normalized localized orbit piece at
  the cycle is `rightPhiSubobject T ψ k r ⋙ toRep`;
- `E₁ = rightPhiIdentityPiece_iso T ψ k r` (published,
  `MirabolicProductMinusRightPhiIdentity`): the piece at the identity is
  `rightPhiQuotient T k (r+1) ⋙ toRep`.

`rightPhiShortExact_of_pieces` transports the middle term to compact induction
from `H`, applies the published localized two-orbit Mackey sequence
`exists_exact_phiMinusUnnormalized_compactInduction` of `MirabolicPhiMinusMackey`
with the normalization twist, replaces the two pieces
by `E₀` and `E₁`, and lifts the natural transformations and their exactness
through the full inclusion of smooth representations. The universes of `E₀`,
`E₁` and the clause agree; the coverage theorem is used at the topology
`T.generalLinearTopologicalGroup (k+r+3)`, which is the instance
`T.generalLinearTopologicalGroup (k+r+1+1+1)` of the assembly.

## The cyclic piece

The three helper modules of this unit compute `E₀`; their Markdown describes
each declaration:

- `MirabolicProductMinusRightPhiCycleGroups`: the cyclic stabilizer `S`, the
  section subgroup `K = P.comap plusSuccessor` in lower right mixed coordinates
  `[[p, X], [0, a]]` (shape `(k+1, r)`), `S ∩ ker plusProjection ≅ rightPsiKernel
  (k+1) (r+1)`, the positive character on it equal to `θ_r` (published
  `rightOrbitTheta_zero`), and the Haar ratio `|det a|`;
- `MirabolicProductMinusRightPhiCycleCoefficient`: the `θ`-localized tensor
  coinvariants of the case (III) coefficient, the localized coefficient
  `≅ τ_(V_(r+2), θ_r) ⊗ ρ` (the carrier of `Φ⁻τ ⊗ ρ`), its section action,
  naturality and the scalar identity
  `ν(p)^(-1/2) ν(a)^(-1/2) · ν(a) · ν(p)^((k+1)/2) ν(a)^(-(r+2)/2) =
  ν(p)^((k+1)/2) ν(a)^(-(r+1)/2) · ν(p)^(-1/2)`;
- `MirabolicProductMinusRightPhiCycle`: the chain plusPhiLocalization →
  localized action → published `SplitStagesCharacter.comparisonEquiv` → `Φ⁻`
  twist → `compactInducedTransport` along the rank cast to
  `rightSubgroup (k+1) r`, natural in both inputs, and `mirabolicRankCastIso`.

## Mathematical dependency and restriction audit

This unit consists of this module and the three helper modules
`MirabolicProductMinusRightPhiCycleGroups`,
`MirabolicProductMinusRightPhiCycleCoefficient` and
`MirabolicProductMinusRightPhiCycle`, each with its own Markdown. All other
inputs are independently accepted and published at Library commit
`2927ec07fc7e178bab9e51306772905c3dc33579`. No Library module is modified.
Proposition definitions in the closure supply types and constructions; none is
used as a proof of its conclusion.

| Condition | Actual dependency and scope |
| --- | --- |
| Orbit coverage | The published proof `mirabolicMixedOrbitCoverage` (`MirabolicMixedOrbitCoverageProof`, with the elementary entrywise lemmas of `MirabolicMixedOrbitSpecializations`) supplies the ordered two-orbit enumeration. It is an independently accepted elementary matrix computation; its statement module is a proposition definition used only as the type of that proof. |
| Identity piece and assembly | The published `rightPhiIdentityPiece_iso` (`MirabolicProductMinusRightPhiIdentity`) and `rightPhiShortExact_of_pieces` (`MirabolicProductMinusRightPhiAssembly`), with `MirabolicProductMinusRightPhiIdentityGroups` and `…IdentityCoefficient`, are accepted and published lower results; the assembly keeps its enumeration and piece isomorphisms as explicit premises, all supplied here by proofs. |
| Localized compact induction | The published `SplitStagesCharacter.comparisonEquiv`, `coefficientAction_mk` and `comparisonEquiv_natural` (proof of the published `SplitStagesCharacterComparisonStatement`) are used with the actual groups, character and coefficient at the cycle. All their hypotheses are proved in this unit. No comparison or bijectivity premise is assumed. |
| Mackey sequence | `MirabolicPhiMinusMackey` (published) supplies `plusPhiLocalization`, `plusKernelTheta` and, in the assembly, the localized two-orbit sequence. |
| Orbit data and characters | `MirabolicMixedOrbitData`, `…Stages`, `…Sections`, `…SectionCoefficients` and `…Radicals` (published) supply the representatives, stabilizers, sections, radical intersections and coefficient formulas. `MirabolicMixedOrbitCharacters` (published) is used only for `rightOrbitTheta_zero`, an elementary character calculation on the cyclic radical intersection. |
| Haar ratio and normalization | The ratio `|det a|` is computed from the published `mulEquivHaarChar_conj_levi_inv` and kernel identifications. The `Φ⁻` normalizations on `P_(k+r+2)` and `P_(r+1)` and the case (III) characters of shapes `(k+1, r+1)` and `(k+1, r)` are the actual published characters, and the real-power identity is proved (published `rightPsi_scalar_identity_complex`). No residual twist is assumed. |
| Coefficient tensor quotient | The `θ`-localized identification is proved here from quotient universal properties and the published `rightPsiInducingCoefficient_kernel`. No finiteness conclusion is used. |
| Right Psi and right boundary modules | `MirabolicProductMinusRightPsi`, `…RightPsiGroups`, `…RightPsiCoefficient` and `…RightBoundary` (published) supply lower lemmas (compact open bases, `compEquivOfEq`, `compactInductionTwistEquiv_natural`, `rightPsiKernel`, `rightPsiKernelEquiv`, `mirabolicCastHom`, `mirabolicRankCastIso`, radical bases, Haar moduli). Their clause theorems `rightPsiCompatibility` and `rightPhiBoundary` are not used. |
| Restriction-sequence modules | `MirabolicProductRestrictionTransport` supplies only `compactInducedTransport`; `MirabolicProductRestrictionMackey` (through the Mackey module) supplies only `RepFunctorFiltration.exists_exact_of_two`. No BZ77 4.13(a) conclusion is used. |
| Unimodularity and quotient measures | `Haar.compactOpenCoverUnimodularity` and `QuotientIntegration.compatibleMeasureExists` are measure-theoretic results on locally compact groups. |
| Plus functors and adjunction | From `MirabolicPlus` only the character `thetaPlus` and its laws are used (here through `plusKernelTheta` and `thetaPlus_rightCycle`). No plus functor, plus/minus adjunction or plus-functor conclusion is used. `Induction.StructuralStatement` (through `CharacterTwistProof`) supplies only proposition definitions, including `OpenSubgroupAdjunctionClause`; none is used as a proof. |
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
| Host clauses and pending results | The compatibility statement module supplies only the unchanged proposition and functor definitions. No other host clause theorem is used; in particular no left `Ψ⁻` or `Φ⁻` comparison, left boundary, right `Ψ⁻` clause or right boundary theorem. No pending candidate, draft or consumer conclusion is imported or used. |
| Parameters and run controls | `T`, `ψ`, `k`, `r` and all smooth input carriers, including zero objects, are arbitrary. No suspended or paused worker supplies or waives an obligation. |

These rows cover every named task in the host's inherited exclusion union, its
mathematical conclusions, proof successors and downstream consequences. A
search over the source of the complete closure below and of this module found
no excluded declaration name and no task identifier in Lean code; the only
match of `admit` is English text in a docstring of
`Geometric.ClosedSubgroupStatement`. The search found no `sorry`, `native_decide`
or new axiom. The theorem `rightPhiShortExact` depends only on `propext`,
`Classical.choice` and `Quot.sound`.

## Complete project import closure

There are exactly 255 transitive project imports, excluding this module, at
Library base `2927ec07fc7e178bab9e51306772905c3dc33579`, computed from the
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
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
Langlands.Representation.Derivative.MirabolicPhiMinusMackey
Langlands.Representation.Derivative.MirabolicPlus
Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary
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
