# Actual left mixed-product identity localization

Author: Worker 499.

This module constructs `leftPhiProductIdentityIso` in
`Langlands.Derivative.MirabolicProductMinus`. The actual normalized Phi-minus
of the higher left mixed product, viewed in `Rep`, is naturally isomorphic
to the entire normalized positive-character localization of the actual
identity orbit. Its forward map uses the published actual Mackey projection.
Both original representation inputs, the full quotient carriers, all
normalization characters and the published rank transport are retained.

The lower source-Phi comparison and its packaging as the host
`LeftPhiCompatibility` remain separate. This focused construction does not
prove the six-part `MirabolicProductMinusCompatibilityStatement`.

## Original source and derived provenance

The original motivation is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, registered as `bernstein-zelevinsky-1977-induced-i`. The retained
original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8(b) and Proposition 1.9(f), printed pp.444–445 (one-based PDF
pages 5–6), give the character quotient, inverse-half normalization and
character-twist comparison. Sections 3.1–3.2, printed pp.450–451 (PDF
pages 11–12), define the mirabolic groups and minus functors. Section
4.12(II), printed pp.456–457 (PDF pages 17–18), defines the left mixed
product. Section 4.13(b), printed p.458 (PDF page 19), states its natural
minus compatibility, and §7.2, printed p.471 (PDF page 32), describes the
two left orbits. These passages and relevant page images were read during
this task. The bounded supplied-source and public-note errata search
found no applicable BZ77 entry; no global absence is asserted.

The present functor packaging and composition are internal derived content.
The original does not state these exact Library interfaces. The proof
composes three independently published constructions: transport of the
actual higher product into ambient compact-induction coordinates, the
full normalized Phi-minus/kernel comparison, and the natural localized
Mackey projection. The last input already proves its projection bijective
from the actual two-orbit sequence, right exactness and full cycle
vanishing. None of those results is assumed from BZ77's unformalized
compatibility conclusion. The pending identity-to-lower-source comparison
is not an input.

## Parameters, ranks and normalization

The two public definitions quantify arbitrary `{p : ℕ} [Fact p.Prime]`,
`{F : PadicField.{uF} p}`, supplied `T : F.TopologicalData`, the bundled
continuous nontrivial unitary additive character
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`, and `k r : ℕ`.
The input category is exactly

```text
SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k+1) F.Carrier)
  × SmoothRep.{0,uF,uV} ℂ (mirabolic (r+1) F.Carrier).
```

The field and coefficient universes `uF,uV` are independent. The output
carrier universe is `max uF uV`, as required by actual compact induction.
The installed topology is exactly `T.topology`; the ambient
topological-group instance is `T.generalLinearTopologicalGroup (k+r+3)`.
No admissibility, irreducibility, finite dimension, finite length,
genericity, chosen vector, canonical topology, universe saturation or
theorem-valued premise is introduced. Zero representations and all
infinite-dimensional smooth carriers are included.

The Library convention is `mirabolic n F.Carrier = P_(n+1)(F)`. Thus the
positive GL input has rank `k+1`, the source mirabolic representation is
on `P_(r+2)`, the higher product is on `P_(k+r+3)`, and ambient Phi-minus
lands on `P_(k+r+2)`. The actual source rank transport is the published
`mirabolicRankCast T (Nat.succ_add k (r+1))`; its target index
`k+(r+1)+1` is definitionally `k+r+2`. The host-induction comparison uses
the proof `totalRank_eq k r` of the same rank equality. Proof irrelevance
identifies these equality proofs without discarding the rank cast.
All `k,r`, including zero, are allowed; no `P_0` or Phi-minus on `P_1`
is introduced. The source-rank-one boundary is outside this construction.

Write

```text
G = mirabolic (k+r+2) F.Carrier,
H = leftInducing k r F.Carrier,
Q = plusSubgroup (k+r+1) F.Carrier,
L = mirabolic (k+r+1) F.Carrier,
p = plusProjection : Q →* L,
s = plusSuccessor : L →* Q,
θ = plusKernelTheta ψ (k+r+1),
χ = Mirabolic.phiMinusCharacter T (k+r+1),
I = leftPhiMackeyInput T k r.
```

The elementary subgroup, projection and section here are not plus
representation functors. The ambient normalization `χ` is the actual
published determinant inverse-half character with proved open kernel.
`I` is the full tensor coefficient, pulled back along `leftProjection`,
twisted by the actual positive covariance
`T.leftCharacter (k+1) (r+1)`, and pulled back along `leftInducingHom`.
Its scalar is the complete higher covariance
`ν_(k+1)^((r+2)/2) · ν_(r+2)^(-(k+1)/2)`. No character factor is suppressed.

## The full normalized identity functor

`leftPhiNormalizedIdentityPiece T ψ k r` is exactly

```text
(I ⋙ orbitPiece H Q (leftRepresentative k r F.Carrier 1)
   ⋙ leftPhiPlusKernelFunctor T k r ψ) ⋙ χ.twistFunctor.
```

The identity representative has index `1`; the cycle has index `0`.
For an input pair `X`, let
`σ = leftPhiNormalizedStabilizer T k r X.1.representation X.2.representation 1`
and `S = leftStabilizer k r F.Carrier 1`. Its representation is

```text
twist χ (localizedAction p s θ
  (plusKernelTheta_sectionInvariant ψ (k+r+1))
  (compactInduced S σ)).
```

The carrier is the whole positive-character quotient of the actual
`CompactFunctions S σ`: covariant functions with one uniform open right
stabilizer and compact projected support. The quotient imposes every
relation `π(u)z − θ(u) • z` for `u : p.ker`, and retains every quotient
class. Its action is the actual successor section action followed by
the complete ambient twist. Maps are the corresponding compact-induced
maps, section quotient maps and twist maps of both original input maps.

## Implemented natural isomorphism

The exact exported type is

```text
leftPhiProduct.{uF,uV} T ψ k (r+1) ⋙ SmoothRep.toRep
  ≅ leftPhiNormalizedIdentityPiece T ψ k r.
```

The private `leftPhiProductAssociationIso` is the inverse of the ordinary
functor associator for the actual higher product, its equality rank cast
and ambient Phi-minus. A second associator moves `SmoothRep.toRep` to
the right of Phi-minus. Both are natural identity rearrangements; they
keep every actual functor and rank transport.

Set `J = I ⋙ SmoothRep.toRep ⋙ compactInductionFunctor H`. The three
substantive comparisons are:

1. `e₁` is `leftPhiHostInductionIso` whiskered by the actual ambient
   `Mirabolic.phiMinus T ψ (k+r+1) ⋙ SmoothRep.toRep`. The host's smooth
   inducing coefficient functor and `I` have definitionally identical
   objects, maps and functor laws, so the displayed intermediate is `J`.
2. `e₂` whiskers the inverse of `phiMinusNormalizedKernelIso` on the
   left by `J` and on the right by `SmoothRep.toRep`. Its target is
   definitionally the full restriction `restrictedCompactInduction H Q`,
   followed by positive-kernel localization and `χ.twistFunctor`.
   The published kernel comparison removes redundant subgroup membership
   from the full relation-span quotient and retains every class and its
   action. This step includes the entire inverse-half normalization.
3. `e₃` is `leftPhiMackeyLocalizedIso` whiskered by `χ.twistFunctor`.
   Its forward component is the published localized natural Mackey
   projection from the entire restricted induction onto the actual
   identity-orbit induction. Right exactness and vanishing of the entire
   localized cycle give its inverse on the full quotient. The ambient
   twist preserves that complete natural isomorphism.

The definition composes the two associators with `e₁`, `e₂` and `e₃`.
The last step unfolds only the named target functor and uses
`with_reducible exact` to check this same composition. Explicit associators
and typed intermediates control elaboration of dependent rank casts; they
introduce no equality assumption or new mathematical premise.

All inputs and outputs are actual functors on the entire product category.
Whiskering and composition of the published natural isomorphisms prove
naturality for every morphism pair at once. Their inverses, equivariance,
and both inverse identities are part of the exported `NatIso`. Thus the
result is more than an objectwise bijection, and no choice of quotient
representatives, selected input vectors or semisimplification is used.
`SmoothRep.toRep` retains the full carrier, action and all morphisms; the
target here is `Rep` because the published orbit localization has that
interface. Packaging the lower-source identification back in `SmoothRep`
remains a subsequent obligation.

## Import and mathematical dependency audit

The three direct imports are

```text
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHostTransport
Langlands.Representation.Derivative.MirabolicProductMinusPhiKernelComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiMackeyLocalization
```

The full project import closure contains 227 modules, excluding this
entry. All 454 imported Lean/Markdown files are nonempty, unchanged
and verified against the published Library manifest at commit
`fe1d50ac5fc58387b768e0341e76ab0f3146bf25`. All three direct comparison inputs are independently accepted
and public. The complete project closure and external import boundary
appear below.

The direct mathematical inputs are the actual high compact-induction
transport, normalized kernel equivalence, localized Mackey projection,
and ordinary functor associators. Transitively the Mackey input uses
proved two-orbit coverage, the independently proved closed-subgroup
restriction sequence, full character-localization right exactness, the
full positive-character stages comparison and cycle vanishing. Those
in turn use explicit matrix subgroup and determinant calculations,
smooth tensor and character twists, relation-span quotient transport,
compatible Haar quotient measures, compact averaging, local sections,
compact-induction transitivity, and the proved lower kernel/local-inverse
arguments. Host transport uses the actual generic compact-function
transport along the continuous rank equivalence. Kernel comparison uses
the actual radical/kernel equivalence and full quotient naturality.

The host proposition module is imported as a source of the exact
`leftPhiProduct` definition, and its unproved proposition definitions
supply no comparison. Imported finiteness and irreducibility interfaces
supply no representation hypothesis or consumer conclusion.

| Condition | Actual dependency finding |
| --- | --- |
| Exact six host conclusions | The target's proposition definitions and actual functor definitions are imported. No host compatibility or boundary theorem is used. This unit proves the full higher-product-to-identity localization only. |
| Plus functors, adjunction and §4.13(d) | No plus representation functor, adjunction, submodule-detection result or conclusion supplies an input. The plus subgroup, projection and successor are elementary matrix constructions. |
| General Leibniz and derivative formulas | No general Leibniz theorem, unproved BZ77 comparison, Ze80 §3.5 or §9.6 formula, or segment derivative formula is used. |
| Individual head and socle existence | Neither individual special-head/reverse-socle nor segment-socle/reverse-head existence supplies an input. |
| Linked and unlinked segment conclusions | No unlinked irreducibility, linked reverse-product structure, pair reducibility, juxtaposed reverse-product structure or reverse-product quotient homomorphism is used. |
| Segment products, commutation and gluing | No segment-socle product irreducibility, adjacent swap, two-segment commutation, linked-segment gluing, Ze80 4.2 or 9.7 criterion, or consequence is used. |
| Segment Jacquet formulas | No full, head, socle or special-exponent Jacquet formula, successor or downstream conclusion supplies an input. |
| Special-head criterion and generic uniqueness | Neither special-head product irreducibility nor generic segment-product uniqueness is used. |
| Ordered existence, coverage and exhaustion | No ordered multisegment-socle or strong-head existence, socle or special-head exhaustion, quotient coverage or ordered conversion is used. |
| Analytic, tempered and square-integrable classification | No analytic segment classification, forward special essential square-integrability, tempered uniqueness, square-integrable Langlands classification, square-integrable or regular exhaustion, or Ze80 9.3 conclusion is used. |
| Two-supercuspidal consumers | Neither nonadjacent-product irreducibility, two-supercuspidal product structure nor full-product assembly is used. No parent six-statement conclusion (b),(d),(e),(f) is used. |
| Supercuspidal and all-character finiteness | No supercuspidal, all-character single-block or arbitrary-character coinvariant-finiteness theorem or downstream consequence is used. |
| Other Whittaker finiteness | No irreducible or Levi-cuspidal coinvariant-finiteness conclusion or prohibited mirabolic finite-length route supplies an input. The quotient-measure and compact-local-section results are lower induction constructions, not those finiteness conclusions. |
| Generality and normalization | All `k,r`, arbitrary supplied `T`, independent `uF,uV`, positive GL input rank, smooth inputs and entire carriers are retained. Both complete positive inducing covariance and ambient inverse-half normalization remain present. |
| Published-input requirement | Every imported pair is public and unchanged. Prop-valued statements, source formulas, drafts, pending identity comparison and consumer tasks supply no unproved premise. |
| Separate owners and controls | This composition reuses the published restriction sequence and exactness results and does not duplicate their ownership. Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and current suspensions remain binding. |
| Actual maps and quotients | The forward map contains the actual natural Mackey quotient on the entire localized induction, with the full inverse from its published bijectivity proof. Both input maps are retained by whiskering and composition. |
| Actual subgroup and rank maps | The actual higher equality rank transport, continuous compact-induction rank transport, kernel/radical equivalence and actual identity stabilizer all remain in the construction. |

A scan of this entry and its complete project closure finds no Lean-code
occurrence of the host's 38 excluded task identifiers or 24 named consumer
declarations, and no proof holes, new axioms or unsafe evaluation commands.
Excluded names in explanatory Markdown are audit prose. The mathematical
dependency inspection above supports the exclusions in addition to the
symbol scan. Successful compilation and declaration inspection do not
replace independent semantic acceptance and publication.

## Complete project import closure

Every direct and transitive project import, excluding this entry, follows.
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
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHaar
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHostTransport
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

The complete external import boundary of these project modules follows;
their transitive standard-library imports are supplied unchanged by
the pinned environment.

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
