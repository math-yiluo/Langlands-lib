# Actual left Mackey projection after positive-character localization

Author: Worker 499.

This module constructs `leftPhiMackeyLocalizedIso` in
`Langlands.Derivative.MirabolicProductMinus`. For the actual higher left
mixed-product coefficient, localization of the full restricted compact
induction by the positive plus-kernel character is naturally isomorphic to
localization of its actual identity-orbit piece. The forward map is the
localized natural Mackey quotient. The entire localized cycle piece is
zero, and algebraic right exactness makes this quotient bijective.

This is a focused internal prerequisite toward BZ77 §4.13(b).
Its localization uses the unnormalized successor section action. The
comparison with the actual ambient Phi-minus radical action, its
inverse-half determinant twist, the host rank adapters and the final
mixed-minus compatibility remain separate obligations.

## Source and provenance

The original motivation is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, registered as `bernstein-zelevinsky-1977-induced-i`. The retained
original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8(b) and Proposition 1.9(a), printed pp.444–445 (one-based PDF
pages 5–6), define positive-character localization and give exactness.
Sections 3.1–3.2, printed pp.450–451 (PDF pages 11–12), specify the
mirabolic groups and minus functors. Section 4.12(II), printed pp.456–457
(PDF pages 17–18), defines the left mixed product, and §4.13(b), printed
p.458 (PDF page 19), states its natural compatibility. Section 7.2,
printed p.471 (PDF page 32), gives the left identity and cycle orbit
calculation. These passages and their relevant page images were read
during this task. The bounded supplied-source and public-note errata
search found no applicable BZ77 entry; no global absence is asserted.

The present functorial specialization and assembly are derived content.
The actual orbit coverage, closed-subgroup Mackey support filtration,
two-step natural exact-sequence construction, character-stages comparison,
full normalized cycle-coefficient vanishing, and algebraic localization
right exactness are reused from independently published Lean results.
The original does not literally state the Library's nested kernel or
chosen-natural-transformation interfaces. No host comparison, source
formula treated as a theorem, pending candidate or peer draft supplies a
proof body. The generic two-step result is imported from the separate
binary-restriction development; its binary restriction conclusion is not
used as a comparison for this actual mixed restriction.

## Parameters, groups and exact coefficient

The declarations quantify arbitrary `{p : ℕ} [Fact p.Prime]`,
`{F : PadicField.{uF} p}`, supplied `T : F.TopologicalData`, and
`k r : ℕ`. Exactly `T.topology` is installed, with its supplied matrix
topological-group structures. The character
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology` includes continuity
and nontriviality. The input category is

```text
SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k+1) F.Carrier)
  × SmoothRep.{0,uF,uV} ℂ (mirabolic (r+1) F.Carrier).
```

Thus the GL factor has positive rank `k+1`, the source mirabolic factor
is P_(r+2), and `mirabolic n F.Carrier` means P_(n+1). All `k,r`,
including zero, remain allowed. The ambient group is
G = `mirabolic (k+r+2) F.Carrier`, namely P_(k+r+3).
Put

```text
H   = leftInducing k r F.Carrier,
Q   = plusSubgroup (k+r+1) F.Carrier,
L   = mirabolic (k+r+1) F.Carrier,
a   = plusProjection : Q ->* L,
s   = plusSuccessor : L ->* Q,
θ   = plusKernelTheta ψ (k+r+1),
w_i = leftRepresentative k r F.Carrier i,
H_i = orbitStabilizer H Q w_i = leftStabilizer k r F.Carrier i.
```

Here `w_0` is the cycle and `w_1` the identity. The group `L` is
P_(k+r+2), the expected ambient Phi-minus output group. The source
convention `phiMinus T ψ r : P_(r+2) → P_(r+1)` is preserved, but
this unit does not yet invoke that functor on the mixed product. No P_0
or application of Phi-minus to P_1 is introduced.

For an input `X=(ρ,τ)`, `leftPhiMackeyInput` is the existing smooth
external tensor functor, followed by pullback along `leftProjection`,
twist by the entire covariance character
`T.leftCharacter (k+1) (r+1)`, and continuous pullback along
`leftInducingHom k r F.Carrier`. Write its value as A_X. Its carrier is
the full tensor of both input carriers. Restriction along
`stabilizerToInducing H Q w_i` is definitionally
`leftPhiNormalizedStabilizer T k r ρ.representation τ.representation i`.
The input maps are the actual tensor intertwiners with the same pullbacks
and twist. Smoothness is supplied by those published smooth functors.

The universes `uF,uV` are independent. Compact induction raises the
output carrier universe to `max uF uV`. All smooth input objects and
all maps in both factors are retained. There is no admissibility,
irreducibility, dimension, finite-length, genericity, nonzero-input,
selected-vector or universe-saturation premise.

## Actual natural two-orbit sequence

`leftPhiMackey_exists_exact` constructs natural transformations, on all
smooth H-representations,

```text
i : orbitPiece H Q w_0 -> restrictedCompactInduction H Q,
q : restrictedCompactInduction H Q -> orbitPiece H Q w_1,
```

and proves component injectivity of `i`, equality of its linear range
with the kernel of `q`, and component surjectivity of `q`. The middle
carrier is the full compact induction from H to G restricted to Q.
The orbit carrier is compact induction from H_i to Q of the actual
conjugated coefficient. All are the published complete covariant
function carriers, with a uniform open right stabilizer and compact
projected nonzero support.

The proof installs the supplied Hausdorff, nonarchimedean, locally compact
and sigma-compact structures on `GeneralLinear (k+r+3) F.Carrier`.
The ambient mirabolic is closed, giving local compactness and
sigma-compactness on G. The actual H and Q are closed. The first
component of the published `mirabolicMixedOrbitCoverage F T` supplies
an ordered covering with representatives exactly `w_0,w_1`. The
published `closedSubgroupMackeyFiltration` identifies the two actual
support-graded functors with their orbit functors. Rewriting the
representatives and applying
`RepFunctorFiltration.exists_exact_of_two` yields the sequence.
No orbit ordering or representation-theoretic exactness is assumed.

`leftPhiMackeyInjection` and `leftPhiMackeyProjection` choose one such
pair of natural transformations once on the whole category.
`leftPhiMackey_exact` retains the three component properties for this
same pair. Their naturality is part of their chosen types, rather than
an objectwise choice of unrelated maps.

## Positive kernel localization and full cycle vanishing

`leftPhiPlusKernelFunctor` sends a Q-representation B to

```text
Rep.of (localizedAction a s θ
  (plusKernelTheta_sectionInvariant ψ (k+r+1)) B.ρ).
```

Its carrier is the actual character quotient `Coinvariants B.ρ a.ker θ`.
Its L-action is the published successor section action, and its map on
an intertwiner is exactly `sectionMap a s θ invariance`. The published
identity and composition formulas for this map prove the functor laws.
These are elementary subgroup localization constructions; no plus
representation functor is used.

`leftPhiMackeyLocalizedCycle_subsingleton` proves that this functor sends
the entire cycle orbit for A_X to a subsingleton carrier. First it makes
the actual localized compact-induction quotient explicit. The actual
cycle coefficient is smooth by continuous stabilizer pullback of the
smooth A_X. The published `padic_leftPhiStagesCharacterEquiv` identifies
this full localization with compact induction of
`leftPhiStagesAction k r ψ 0` on the actual nested intersection quotient.
The published `leftPhiNormalizedStagesQuotient_zero_subsingleton` makes
that whole coefficient carrier subsingleton for the complete higher
covariance-normalized coefficient. Hence every target compact function
is equal to zero pointwise. Injectivity of the published stages
equivalence transfers subsingletonness to the full localized cycle.
The result is not restricted to generators or selected function supports.

## Algebraic right exactness and the natural isomorphism

The private helper `sectionMap_bijective_of_subsingleton` works for
arbitrary groups G,L, complex representations and intertwiners
`i : ρ → σ`, `q : σ → τ`. It assumes actual surjectivity of q,
`range i = ker q`, and subsingletonness of the actual character
localization of ρ. It concludes bijectivity of the actual section map
induced by q.

It applies the published `Jacquet.Localization.map_range_eq_ker` and
`map_surjective` at acting normalizer subgroup `⊥`. Character invariance
there is proved by its identity element. Their underlying maps are
definitionally the same character-quotient linear maps as `sectionMap`.
For injectivity, equality of two images puts their difference in the
localized kernel. Middle exactness writes that difference as the image
of a localized source element. Subsingletonness makes that element
zero, so the difference is zero. Surjectivity is the published
right-exactness lemma. This argument uses no localization injectivity,
compact-subgroup containment or additional smoothness premise.

`leftPhiMackeyLocalizedProjection` precomposes the chosen natural
Mackey quotient with `leftPhiMackeyInput` and postcomposes it with
`leftPhiPlusKernelFunctor`. For every input X,
`leftPhiMackeyLocalizedProjection_bijective` applies the helper to the
same chosen Mackey maps and the full localized cycle vanishing.

Finally `leftPhiMackeyLocalizedIso` uses `LinearEquiv.ofBijective` on
that actual quotient component, whose intertwining law is already the
one of the localized Mackey map, and packages it with `Rep.mkIso` and
`NatIso.ofComponents`. The naturality equation is exactly the naturality
of the localized projection. In particular, the forward map of the
resulting natural isomorphism is the actual localized Mackey projection,
and it is natural in both original representation inputs.

## Import and mathematical dependency audit

The five direct imports are listed in the audit below. Every one is
published. The complete closure contains 217 imported project modules,
excluding this entry. All 434 imported Lean/Markdown files are nonempty,
byte-identical to the Library and verified against its manifest at commit
`1741653e5f4f861282ff64d062269adbcc65c686`. There is no pending import;
in particular, the host transport adapter is not used.

The direct proof inputs are the actual mixed orbit coverage, closedness
and matrix topology; the published generic Mackey support filtration
and two-step natural sequence; the complete smooth higher coefficient;
elementary positive kernel localization and section maps; the published
full actual stages equivalence and normalized cycle quotient vanishing;
and algebraic localization right exactness. Transitively these use
elementary matrix and determinant calculations, tensor and quotient
algebra, compact covariant section extension, compatible quotient Haar
measures, split-stages quotient integrals and compact averaging.

The imported exactness proof also contains its separate averaging-based
injectivity theorem; that theorem is not used here. Supercuspidal,
admissibility, contragredient, Rankin–Selberg and Whittaker infrastructure
in the closure supplies elementary definitions or lower compact-function
machinery, without any prohibited classification or finiteness conclusion.
The actual proof route above, in addition to the full closure scan,
establishes the following dependency findings.

| Condition | Actual dependency finding |
| --- | --- |
| Six host conclusions | The host statement and proof modules are absent. No host mixed-minus comparison or boundary conclusion supplies an input. This unit proves the localized identity-orbit projection isomorphism only. |
| Plus functors, adjunction and §4.13(d) | None supplies an input. The plus subgroup, projection, successor and positive kernel character are elementary matrix constructions. |
| General Leibniz and derivative formulas | No Leibniz theorem, unproved BZ77 comparison, Ze80 §3.5 or §9.6 formula, or segment derivative formula is used. |
| Individual head and socle existence | Neither individual special-head/reverse-socle nor segment-socle/reverse-head existence supplies an input. |
| Linked and unlinked segment conclusions | No unlinked irreducibility, linked reverse-product structure, pair reducibility, juxtaposed reverse-product structure or reverse-product quotient homomorphism is used. |
| Segment products, commutation and gluing | No segment-socle product irreducibility, adjacent swap, two-segment commutation, linked-segment gluing, Ze80 4.2 or 9.7 criterion, or consequence is used. |
| Segment Jacquet formulas | No full, head, socle or special-exponent Jacquet formula, successor or downstream conclusion supplies an input. |
| Special-head criterion and generic uniqueness | Neither special-head product irreducibility nor generic segment-product uniqueness is used. |
| Ordered existence, coverage and exhaustion | No ordered multisegment-socle or strong-head existence, socle or special-head exhaustion, quotient coverage or ordered conversion is used. |
| Analytic, tempered and square-integrable classification | No analytic segment classification, forward special essential square-integrability, tempered uniqueness, square-integrable Langlands classification, square-integrable or regular exhaustion, or Ze80 9.3 conclusion is used. |
| Two-supercuspidal consumers | Neither nonadjacent-product irreducibility, two-supercuspidal product structure nor full-product assembly is used. No parent six-statement conclusion (b),(d),(e),(f) is used. |
| Supercuspidal and all-character finiteness | No supercuspidal, all-character single-block or arbitrary-character coinvariant-finiteness theorem or downstream consequence is used. |
| Other Whittaker finiteness | No irreducible or Levi-cuspidal coinvariant-finiteness conclusion or prohibited mirabolic finite-length route supplies an input. |
| Generality and normalization | Arbitrary supplied T, all k,r, positive GL rank, independent field and carrier universes and all smooth input objects/maps are retained. The complete higher covariance twist is present; the ambient inverse-half Phi twist remains a separate comparison. |
| Published-input requirement | Every imported pair is published and unchanged. Statements, source formulas, drafts, pending candidates and consumer tasks provide no unproved comparison premise. All comparisons actually invoked are published proofs. |
| Separate owners and controls | The generic restriction/Mackey and exactness results are reused rather than reproved. Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and current suspensions remain binding. |
| Entire carriers and actual maps | The vanishing concerns the whole localized cycle. The isomorphism uses the actual chosen natural Mackey projection and actual character-quotient maps on all elements. |

A scan of this module and its complete project closure finds no Lean-code
occurrence of the host's 38 excluded task identifiers or 24 named consumer
declarations, and no proof holes, new axioms or unsafe evaluation commands.
Names in explanatory Markdown are audit prose. Development compilation is
separate from independent semantic acceptance and publication.

## Complete project import closure

The following direct and transitive project imports exclude this entry.
The approved environment pins Lean and Mathlib respectively to commits
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and
`5ed2965256430c3649e86755f9576b54eca72435`. Its external import boundary
is also listed below; the transitive standard-library closure is supplied
by that unchanged environment.


Direct imports:

```text
Langlands.Group.GL.MirabolicMixedOrbitCoverageProof
Langlands.Representation.Derivative.MirabolicProductRestrictionMackey
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiStagesComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
Langlands.Representation.Jacquet.LocalizationExactnessProof
```

Full project closure:

```text
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
Langlands.Group.GL.UpperUnipotent
Langlands.Group.HaarModulus
Langlands.HarmonicAnalysis.AlgebraicIntegral
Langlands.HarmonicAnalysis.AlgebraicIntegrand
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.Conductor
Langlands.HarmonicAnalysis.HaarConjugacy
Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicLatticeTopology
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.LocalFactor.Harmonic.Statement
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
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
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDeterminant
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHaar
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiStagesComparison
Langlands.Representation.Derivative.MirabolicProductRestrictionMackey
Langlands.Representation.Derivative.MirabolicProductRestrictionOrbits
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
Langlands.Representation.Mirabolic.MixedProducts
Langlands.Representation.OrbitSpan
Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement
Langlands.Representation.RankinSelberg.QuotientIntegrals
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
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.ConjugationStabilizer
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.Nonarchimedean.Subgroup
```

Complete external import boundary:

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Finprod
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.Group.Equiv.TypeTags
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Module.ULift
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Algebra.Ring.GeomSum
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Circle
Mathlib.Analysis.Fourier.FourierTransform
Mathlib.Analysis.InnerProductSpace.Defs
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Complex.Circle
Mathlib.Analysis.SpecialFunctions.Pow.Complex
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Products.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.Data.Fin.Rev
Mathlib.Data.Int.LeastGreatest
Mathlib.Data.Matrix.Block
Mathlib.FieldTheory.Finite.Basic
Mathlib.GroupTheory.Coset.Defs
Mathlib.GroupTheory.DoubleCoset
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.GroupTheory.GroupAction.Quotient
Mathlib.GroupTheory.Subgroup.Centralizer
Mathlib.LinearAlgebra.Dual.Lemmas
Mathlib.LinearAlgebra.Isomorphisms
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Function.LocallyIntegrable
Mathlib.MeasureTheory.Function.SimpleFunc
Mathlib.MeasureTheory.Group.Integral
Mathlib.MeasureTheory.Integral.Bochner.Basic
Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Integral.Prod
Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.MeasureTheory.Measure.Haar.DistribChar
Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
Mathlib.MeasureTheory.Measure.Regular
Mathlib.MeasureTheory.Measure.Typeclasses.Finite
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Atoms
Mathlib.RepresentationTheory.Basic
Mathlib.RepresentationTheory.Coinduced
Mathlib.RepresentationTheory.Coinvariants
Mathlib.RepresentationTheory.Intertwining
Mathlib.RepresentationTheory.Invariants
Mathlib.RepresentationTheory.Irreducible
Mathlib.RepresentationTheory.Rep.Basic
Mathlib.RepresentationTheory.Rep.Res
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.Finiteness.Basic
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.SimpleModule.Basic
Mathlib.RingTheory.Valuation.Integral
Mathlib.Tactic.Linarith
Mathlib.Tactic.NoncommRing
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.OpenMapping
Mathlib.Topology.Algebra.Group.Pointwise
Mathlib.Topology.Algebra.Group.Quotient
Mathlib.Topology.Algebra.Group.Subgroup
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.MulAction
Mathlib.Topology.Algebra.Nonarchimedean.Basic
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.ProperAction.Basic
Mathlib.Topology.Algebra.Ring.Compact
Mathlib.Topology.Algebra.Support
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Baire.LocallyCompactRegular
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Compactness.LocallyCompact
Mathlib.Topology.Compactness.SigmaCompact
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.ContinuousMap.CompactlySupported
Mathlib.Topology.Homeomorph.Lemmas
Mathlib.Topology.Homeomorph.Quotient
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyClosed
Mathlib.Topology.LocallyConstant.Basic
Mathlib.Topology.Order.Compact
Mathlib.Topology.UrysohnsLemma
```
