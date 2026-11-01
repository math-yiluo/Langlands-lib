# Natural normalized left mixed-product Phi compatibility

Authors: Worker 499 and Worker 837. Worker 837 contributed the separate
component and naturality declarations for the stabilizer-to-source comparison.

The theorem `Langlands.Derivative.MirabolicProductMinus.leftPhiCompatibility`
proves exactly the published proposition
`Langlands.Derivative.MirabolicProductMinus.LeftPhiCompatibility.{uF,uV} F T`.
The definition `leftPhiCompatibilityIso` constructs the actual natural
isomorphism

```text
leftPhiProduct.{uF,uV} T ψ k (r+1) ≅ leftPhiExpected T ψ k r.
```

Thus normalized Phi-minus commutes with the left mixed product when the
source is `P_(r+2)`, naturally in both original representation inputs. The
whole carriers, both input maps, all normalization characters and the actual
rank transports are retained. This is component 2 of the six-part host
statement. The other five clauses and the final conjunction are separate
proof obligations.

## Original source and implemented route

The original source is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, registered as `bernstein-zelevinsky-1977-induced-i`. The retained
original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8(b) and Proposition 1.9(f), printed pp.444–445 (one-based PDF
pages 5–6), give character localization, its normalization and twist
comparison. Sections 3.1–3.2, printed pp.450–451 (PDF pages 11–12), define
the mirabolic minus functors. Section 4.12(II), printed pp.456–457 (PDF
pages 17–18), defines the left mixed product, and Proposition 4.13(b),
printed p.458 (PDF page 19), states this natural compatibility. Section
7.2, printed p.471 (PDF page 32), describes its two-orbit calculation.
These passages and relevant page images were read during this task. The
bounded supplied-source and public-note errata search found no applicable
BZ77 entry; this is not a global absence claim.

The implemented proof composes published full natural and representation
comparisons. Its categorical packaging is internal derived content; the
original does not state these exact Library interfaces. The higher-product
to identity-localization comparison already proves the localized Mackey
projection bijective, using the actual two-orbit sequence, right exactness
and vanishing of the full cycle localization. The identity-to-source
comparison already proves an equivalence on the entire normalized
localization, using character stages, ambient normalization and source
coefficient transport. This file packages those proved comparisons into a
natural isomorphism with the exact host endpoints. BZ77's unformalized
conclusion is never an assumed comparison premise.

## Parameters, ranks and normalization

The complete theorem type has arbitrary `{p : ℕ} [Fact p.Prime]`,
`{F : PadicField.{uF} p}` and supplied `T : F.TopologicalData`, and concludes
exactly `LeftPhiCompatibility.{uF,uV} F T`. The two universes are independent.
Unfolding that proposition quantifies every bundled continuous nontrivial
unitary additive character `ψ` and every `k r : ℕ`, including zero. All
objects and maps are in the full category

```text
SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k+1) F.Carrier)
  × SmoothRep.{0,uF,uV} ℂ (mirabolic (r+1) F.Carrier).
```

Only the supplied topology `T.topology` is used. No admissibility,
irreducibility, finite dimension, finite length, genericity, chosen vector,
canonical topology, universe saturation or theorem-valued premise is added.
Zero inputs and all infinite-dimensional smooth carriers are included. The
output carrier universe is `max uF uV`, as required by actual compact
induction.

The Library convention is `mirabolic n F.Carrier = P_(n+1)(F)`.
Here the GL input is `GL_(k+1)` and the source is `P_(r+2)`; the higher
product is on `P_(k+r+3)`. Ambient Phi-minus lands on `P_(k+r+2)`.
Source Phi-minus is exactly
`phiMinus T ψ r : P_(r+2) → P_(r+1)`.
Both actual host endpoints use their proved equality rank pullbacks. The
higher one is `mirabolicRankCast T (Nat.succ_add k (r+1))`; the lower one
is `mirabolicRankCast T (Nat.succ_add k r)`. The explicit lower inverse
pullback is `leftPhiLowerRankEquiv k r F.Carrier`. Neither rank map is
discarded. No `P_0` or Phi-minus on `P_1` is introduced. The boundary at
source `P_1` is a different host clause.

Put

```text
H = leftInducing k r F.Carrier,
Q = plusSubgroup (k+r+1) F.Carrier,
L = mirabolic (k+r+1) F.Carrier,
S = leftStabilizer k r F.Carrier 1,
p = plusProjection : Q →* L,
s = plusSuccessor : L →* Q,
θ = plusKernelTheta ψ (k+r+1),
χ = Mirabolic.phiMinusCharacter T (k+r+1),
I = leftPhiMackeyInput T k r.
```

The subgroup, projection and successor are elementary matrix constructions.
The higher inducing covariance remains
`ν_(k+1)^((r+2)/2) · ν_(r+2)^(-(k+1)/2)` from the actual positive character
`T.leftCharacter (k+1) (r+1)`. The ambient inverse-half normalization is
exactly `χ`. The target coefficient contains the full lower character
`T.leftCharacter (k+1) r` and the actual normalized source Phi action,
including its inverse-half determinant character. The published identity
comparison proves their scalar compatibility; no residual twist is dropped.

## Stabilizer and source functors

`leftPhiStabilizerFunctor T k r i` sends a pair `X` to `Rep.of` of
`leftPhiNormalizedStabilizer T k r X.1.representation X.2.representation i`.
Its map is the published `leftPhiNormalizedStabilizerMap` of both input
maps. The identity law reduces to `TensorProduct.map_id`, and composition
to `externalMap_comp`. For either orbit index, the private
`leftPhiStabilizerRestrictionIso` identifies the restriction of `I` along
`stabilizerToInducing` with this explicit coefficient. Its component is
the identity linear equivalence; intertwining and naturality are checked
by definitional equality.

`leftPhiStabilizerLocalizedFunctor` compactly induces the identity
coefficient (`i=1`) to `Q`, applies the entire positive-kernel localization,
and twists by `χ`. Its carrier is the whole quotient of the actual
`CompactFunctions S σ` by every relation `π(u)z − θ(u) • z`, for `u : p.ker`.
It keeps every localization class, the successor action, and every input
map. The cycle representative is index `0` and the identity is index `1`.

`leftPhiStabilizerLocalizationIso` identifies the published normalized
identity-orbit functor with this explicit functor. The proof writes out
ordinary functor associators for the smooth inclusion, stabilizer
restriction, compact induction, second inclusion, kernel localization and
twist. It then whiskers `leftPhiStabilizerRestrictionIso` by the last four
functors. All changes here are natural rearrangements of the actual
composition or the proved identity coefficient comparison.

`leftPhiSourceFunctor` sends `X` to `Rep.of` of
`leftPhiSourceCoefficient T k r ψ X.1.representation X.2`. This is precisely

```text
twist (T.leftCharacter (k+1) r).toMonoidHom
  (leftInducingRepresentation X.1.representation
    ((Mirabolic.phiMinus T ψ r).obj X.2).representation).
```

Its map is `leftPhiSourceCoefficientMap`, whose underlying map is the
tensor of the first input map with the actual source Phi quotient map.
The two functor laws use `phiMinus.map_id`, `phiMinus.map_comp`,
`TensorProduct.map_id` and `externalMap_comp`. No replacement of the
source quotient by a selected model is made.

`leftPhiSourceInducedFunctor` compactly induces this full coefficient from
`leftSubgroup (k+1) r F.Carrier`, forgets to `Rep`, and pulls back along
`leftPhiLowerRankEquiv`. Its source carrier is the entire compact-function
space with the lower normalized covariance and actual inverse rank map.

## Complete natural comparison and smooth host endpoint

`leftPhiStabilizerSourceIsoApp` uses the independently published
`leftPhiIdentityNormalizedEquiv` as a `Rep.mkIso` component between the two
explicit functors. Unfolding only their object wrappers exposes the exact
published representations. `leftPhiStabilizerSourceIsoApp_natural`
applies `Rep.hom_ext`, intertwiner extensionality and linear-map
extensionality, then uses
`leftPhiIdentityNormalizedEquiv_natural` for the two arbitrary input maps.
The separate declarations bound elaboration cost; they add no assumption.
`NatIso.ofComponents` combines the components and this naturality square
into `leftPhiStabilizerSourceIso`.

`leftPhiSourceExpectedIsoApp` is the identity isomorphism from the induced
source model to `leftPhiExpectedPullback ⋙ SmoothRep.toRep`: their full
objects are definitionally equal. Its naturality follows by the same
three extensionality steps and reflexivity, since both map formulas are
the same compact-induced tensor/source-quotient map followed by the same
pullback. `leftPhiSourceExpectedIso` packages these identities naturally.
This direct endpoint identity needs no separate coefficient theorem.

`leftPhiCompatibilityIso` composes, in order:

1. `leftPhiProductIdentityIso`, from actual higher-product Phi-minus in
   `Rep` to the full normalized identity localization;
2. `leftPhiStabilizerLocalizationIso`, exposing its stabilizer coefficient;
3. `leftPhiStabilizerSourceIso`, the full normalized identity/source
   comparison with its two-input naturality;
4. `leftPhiSourceExpectedIso`, the actual lower expected pullback;
5. the inverse of `leftPhiExpectedHostIso`, whiskered by `SmoothRep.toRep`,
   returning to the exact published host rank cast.

The inclusion `SmoothRep.toRep` is full and faithful.
`Functor.fullyFaithfulCancelRight` therefore lifts the composite back to
a natural isomorphism between the actual smooth host functors. It retains
the entire underlying intertwiner and its inverse. Finally
`leftPhiCompatibility` supplies this isomorphism for every `ψ,k,r` inside
`Nonempty`, proving the exact existing proposition. The result has actual
natural maps and inverses at every pair, rather than an objectwise list or
a character or Grothendieck-group identity.

## Import and mathematical dependency audit

The three direct imports are HostTransport, Localization and
IdentityComparison, under `Langlands.Representation.Derivative` with prefix
`MirabolicProductMinusLeftPhi`. All three are independently accepted and
published. No pending draft or candidate supplies a mathematical premise.

The complete project import closure contains 231 modules, excluding this
entry. All 462 imported Lean/Markdown files are nonempty, unchanged,
and byte-verified against the published Library manifest at commit
`00315d47b3cf847fb5aa4184c78df11887f7fe20`. The complete closure and external boundary follow below.

Direct mathematical inputs are the published product/identity natural
isomorphism, full normalized identity/source equivalence and its naturality,
actual lower host rank comparison, identity coefficient restriction,
tensor map laws, ordinary functor associators and the full-faithful smooth
inclusion. Transitively these reuse proved two-orbit coverage, the actual
closed-subgroup restriction sequence, full character-localization right
exactness and cycle vanishing, the positive-character stages comparison,
ambient induction twist, source tensor-quotient equivalence, compact
induction transport and transitivity, and their naturality. These lower
proofs use explicit matrices and determinants, smooth restriction and
twists, full relation-span quotient transport, compatible Haar quotient
measures, compact averaging and compact local sections. They introduce no
consumer comparison, finiteness or classification premise.

The host proposition module supplies the exact actual functors and the
proposition being proved. Its other unproved proposition definitions
supply no comparison. Imported admissibility, irreducibility and Whittaker
construction interfaces do not supply any such representation hypothesis
or finiteness conclusion.

| Condition | Actual dependency finding |
| --- | --- |
| Exact host clauses | This file proves only the published `LeftPhiCompatibility`. No other host compatibility or boundary theorem is used. |
| Plus functors, adjunction and §4.13(d) | No plus representation functor, adjunction, submodule-detection result or conclusion supplies an input. The plus subgroup, projection and successor are elementary constructions. |
| General Leibniz and derivative formulas | No general Leibniz proof, unproved BZ77 comparison, Ze80 §3.5 or §9.6 formula, or segment derivative formula is used. |
| Individual head and socle existence | Neither individual special-head/reverse-socle nor segment-socle/reverse-head existence supplies an input. |
| Linked and unlinked segment conclusions | No unlinked irreducibility, linked reverse-product structure, pair reducibility, juxtaposed reverse-product structure or reverse-product quotient homomorphism is used. |
| Segment products, commutation and gluing | No segment-socle product irreducibility, adjacent swap, two-segment commutation, linked-segment gluing, Ze80 4.2 or 9.7 criterion, or consequence is used. |
| Segment Jacquet formulas | No full, head, socle or special-exponent Jacquet formula, successor or downstream conclusion supplies an input. |
| Special-head criterion and generic uniqueness | Neither special-head product irreducibility nor generic segment-product uniqueness is used. |
| Ordered existence, coverage and exhaustion | No ordered multisegment-socle or strong-head existence, socle or special-head exhaustion, quotient coverage or ordered conversion is used. |
| Analytic, tempered and square-integrable classification | No analytic segment classification, forward special essential square-integrability, tempered uniqueness, square-integrable Langlands classification, square-integrable or regular exhaustion, or Ze80 9.3 conclusion is used. |
| Two-supercuspidal consumers | Neither nonadjacent-product irreducibility, two-supercuspidal product structure nor full-product assembly is used. No parent six-statement conclusion (b),(d),(e),(f) is used. |
| Supercuspidal and all-character finiteness | No supercuspidal, all-character single-block or arbitrary-character coinvariant-finiteness theorem or downstream consequence is used. |
| Other Whittaker finiteness | No irreducible or Levi-cuspidal coinvariant-finiteness conclusion or prohibited mirabolic finite-length route supplies an input. Lower quotient-measure and compact-local-section constructions supply no such finiteness conclusion. |
| Generality and normalization | All `k,r`, arbitrary supplied `T`, independent `uF,uV`, positive GL input rank, arbitrary smooth inputs, entire carriers, full covariance and both inverse-half normalizations remain present. |
| Published-input requirement | Every imported pair is public and unchanged. Proposition definitions, source formulas, drafts and consumer tasks supply no unproved premise. |
| Separate owners and controls | The proof reuses the published restriction sequence and exactness results without duplicating their ownership. Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and current suspensions remain binding. |
| Actual maps and quotients | The composite contains the full localized natural Mackey quotient and inverse, full identity/source equivalence and both arbitrary input maps, lifted back into the full smooth category. |
| Actual subgroup and rank maps | Both exact host rank casts, the continuous compact-induction rank maps, actual identity stabilizer and actual radical/kernel relation quotients remain in the proof. |

The complete source scan finds no Lean-code occurrence of the host's 38
excluded task identifiers or 24 named consumer declarations, and no proof
holes, new axioms or unsafe evaluation commands. The condition audit above
also checks mathematical use; a symbol scan alone is not a semantic proof
of independence. Compilation and declaration inspection do not replace
independent semantic review and publication.

## Complete project import closure

All direct and transitive project imports, excluding this entry, follow.
The authorized Lean and Mathlib commits are respectively
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and
`5ed2965256430c3649e86755f9576b54eca72435`.

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
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDeterminant
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
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
Langlands.Representation.Derivative.MirabolicProductMinusPhiKernelComparison
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

The complete external import boundary of the project closure follows.
Its transitive standard-library imports are supplied unchanged by the pinned
environment.

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
Mathlib.Data.Nat.Find
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
