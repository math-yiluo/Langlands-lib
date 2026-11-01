# Actual left-Phi character stages comparison

Author: Worker 499.

This module constructs `leftPhiStagesCharacterEquiv` and its supplied-topology
adapter `padic_leftPhiStagesCharacterEquiv` in
`Langlands.Derivative.MirabolicProductMinus`. At either actual left orbit
representative they identify character-localized compact induction with compact
induction of the entire actual section coefficient. All Haar and quotient
measure data are constructed from the actual groups. The identification is
natural for every stabilizer intertwiner, across independent coefficient
universes. The source and target actions here are the unnormalized section
actions. The ambient inverse-half normalization, normalized source coefficient
comparison, rank transport and six-part host compatibility theorem remain
separate obligations.

## Source and provenance

The original motivation is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, registered as `bernstein-zelevinsky-1977-induced-i`. The retained
original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8(b), printed pp.444–445 (one-based PDF pages 5–6), defines
positive-character localization and its normalizing-subgroup action. Sections
3.1–3.2, printed pp.450–451 (PDF pages 11–12), give the mirabolic positive
character and minus functors. Section 4.12(II), printed pp.456–457 (PDF pages
17–18), defines the left mixed product; §4.13(b), printed p.458 (PDF page 19),
states its functorial comparisons. Section 7.2, printed p.471 (PDF page 32),
gives the two left orbit representatives. These passages and relevant page
images were read during this task. The bounded supplied-source and public-note
errata search found no applicable BZ77 entry; no global absence is asserted.

The present topology, measure construction and specialization of the published
generic comparison are internal derived content. The original does not
literally state the arbitrary-ring adapters or the chosen compatible measure.
The construction imports the published actual section coefficient and actual
Haar-ratio identity, the proved generic character-stages comparison, the proved
compatible quotient-measure existence theorem and the compact-open basis for
matrix groups. No host comparison is assumed. Worker 499 wrote this pair;
no peer draft supplies a proof body. The generic comparison is reused by its
published Lean name.

## Parameters and exact actions

The kernel topology declarations use arbitrary `R : Type uF` with
`[CommRing R]` and `[TopologicalSpace R]`. The measure construction further
uses `[IsTopologicalRing R]`, `[T2Space R]` and local compactness of
`GeneralLinear (k+r+3) R`. The general comparison uses a nonarchimedean
structure on that general linear group, a unitary additive character `ψ`, an
open-kernel proof for its actual plus-kernel character, and a smooth
representation of the actual stabilizer. These are ordinary topology,
character and smoothness conditions, without any assumed comparison.

For every `k,r : ℕ` and `i : Fin 2`, put

```text
G    = plusSubgroup (k+r+1) R,
L    = mirabolic (k+r+1) R,
p    = plusProjection : G ->* L,
s    = plusSuccessor : L ->* G,
P_i  = leftStages k r R i,
H_i  = leftStabilizer k r R i,
K_i  = P_i.comap s,
r_i  = leftPhiStagesRetraction k r i : P_i ->* K_i,
H'_i = leftPhiStagesStabilizer k r i = H_i.subgroupOf P_i,
I_i  = H'_i.comap (ker r_i).subtype,
θ    = plusKernelTheta ψ (k+r+1).
```

Index `0` is the cycle representative and index `1` is the identity.
For an arbitrary smooth `σ : Representation ℂ H_i V`, the source of
`leftPhiStagesCharacterEquiv` is exactly

```text
localizedAction p s θ (plusKernelTheta_sectionInvariant ψ (k+r+1))
  (compactInduced H_i σ).
```

Its underlying module is the full localization of compactly supported
induced functions by the actual kernel character. The target is exactly

```text
compactInduced K_i (leftPhiStagesAction k r ψ i σ).
```

Its coefficient is the full published actual nested intersection quotient,
with the actual section action. No subspace of selected functions or quotient
representatives replaces either carrier. The general coefficient carrier
`V : Type uV` and naturality target carrier `W : Type uW` are independent of
each other and of `uF`. No dimension, admissibility, irreducibility, length,
genericity, nonzero-vector or universe-saturation condition is imposed.

The ambient mirabolic group is `P_(k+r+3)` and the output section group is
`P_(k+r+2)`, using `mirabolic n R = P_(n+1)(R)`. The intended higher left
product has positive GL rank `k+1` and source mirabolic factor `P_(r+2)`.
The host convention `phiMinus T ψ r : P_(r+2) → P_(r+1)` is retained.
All `k,r`, including zero, are allowed. No `P_0` or Phi-minus on `P_1` is
introduced. This unit does not yet identify `K_i` compact induction with a
rank-transported normalized mixed product.

## Topology and measure construction

`plusKernelRadicalContinuousEquiv` removes the redundant plus-subgroup
membership from the actual plus kernel. Its underlying multiplicative
equivalence is `plusKernelRadicalEquiv`; both directions are continuous
subtype maps. The original group and topology are retained.

`leftPhiStagesKernelCommGroup` exposes commutativity of the actual nested
kernel without changing its multiplication or inverse. Its proof transports
the equality of products through `leftPhiStagesKernelEquiv` followed by
`radicalEquiv`, whose additive-coordinate target is commutative. The
construction is an abbreviation retaining the existing `Group` operations.
The helper `measureRightOfComm` proves right invariance from left invariance
by equality of left and right translations. It avoids installing a different
group structure on the nested subtypes.

The kernel is locally compact by `leftPhiHaar_kernel_locallyCompact`.
The intersection `I_i` is closed in this kernel because the actual nested
stabilizer is closed and its inclusion is continuous. It is therefore locally
compact. The actual kernel, intersection and left quotient carry their Borel
measurable structures. The canonical `haar` measures on the kernel and
intersection are regular Haar measures. Both are also right invariant, by
commutativity of the existing kernel operations and their inherited subgroup
operations.

`leftPhi_stagesCompatibleMeasure_exists` applies the published
`QuotientIntegration.compatibleMeasureExists` to precisely these two Haar
measures and this closed intersection. `leftPhiStagesQuotientMeasure` chooses
one resulting measure, and `leftPhiStagesQuotientMeasure_compatible` proves
its actual `IsCompatible` property. The compatibility proof supplies its
regularity, hence finiteness on compact sets. All these choices depend on the
groups, topology and orbit index, independently of `σ`, `τ` or an intertwiner.
Thus naturality uses the same measure on both sides. No equality of arbitrary
measure choices or representation-dependent normalization is assumed.

`actualPlusBasis` obtains compact open subgroups from the published
`compactOpenSubgroupBasis` on the actual plus subgroup. Its local compactness
comes from the closed mirabolic and plus subgroups of the supplied locally
compact matrix group. `actualKernelBasis` applies the same basis theorem to
the actual nested kernel. Its local compactness was derived above. These
are the two bases required by the generic comparison. Closedness of the
ambient plus kernel is the preimage of the closed identity singleton under
`continuous_plusProjection`.

## Actual comparison and full naturality

`leftPhiComparisonTheta` bundles the actual positive kernel character and
its open-kernel proof. The published `plusKernelTheta_sectionInvariant`
supplies its actual section invariance. The generic section-containment
argument is specialized with `leftPhiStagesSection_mem`, over exactly
`P_i.comap s`.

`leftPhiComparisonHaarCharacter_eq_one` identifies the generic stages Haar
character with the actual one and applies `leftPhiStagesHaarRatio_eq_one`.
The equality holds as an entire complex unit-valued character, at both
representatives. This is the actual intersection-to-kernel ratio with the
published orientation. It follows from the proved full kernel containment
in the actual stabilizer; no reciprocal factor or half-density is silently
introduced.

The generic coefficient is the Haar-character twist of the actual section
coefficient. `leftPhiComparisonCoefficientEquiv` uses the identity linear
equivalence on all quotient classes. Its intertwining proof rewrites that
entire character to one. Thus the generic coefficient agrees with the full
actual `leftPhiStagesAction`, without a residual Haar character.

`leftPhiStagesCharacterEquiv` installs the chosen compatible quotient measure
and its regularity. It applies the published
`SplitStagesCharacter.comparisonEquiv` to the actual plus projection and
successor, actual closed stages and stabilizer, their inclusions, actual
section containment, positive character, smooth `σ`, the two derived bases,
and the constructed measures and compatibility proof. It then composes with
`compactInducedEquiv` for the identity-on-class coefficient equivalence.
The generic comparison supplies bijectivity and equivariance; the final
composition removes exactly its now-proved trivial Haar character. The
imported generic proof uses inverse-character twisting, the proved ordinary
split-stages quotient integral and actual quotient transports. No unproved
localization/induction comparison supplies an input.

`leftPhiStagesCharacterEquiv_natural` holds for every
`f : σ.IntertwiningMap τ` and every element `z` of the complete localized
source. Its equation is

```text
E_τ (sectionMap p s θ invariance (compactInducedMap H_i f) z)
  = compactInducedMap K_i (leftPhiStagesMap k r ψ i f) (E_σ z).
```

The proof first specializes the published full generic naturality equation
with the same explicit measures and bases. Applying the target
`compactInducedEquiv` to that equality gives the stated equation; its
identity-on-class underlying map leaves the actual coefficient map
unchanged. The argument is on arbitrary quotient elements and preserves
independent `uV,uW`.

## Supplied p-adic topology

The p-adic section quantifies arbitrary `{p : ℕ} [Fact p.Prime]`,
`{F : PadicField.{uF} p}`, supplied `T : F.TopologicalData` and
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`.
`plusKernelSmoothTheta` pulls the open kernel of
`T.mirabolicTheta_isOpen_ker` back along
`plusKernelRadicalContinuousEquiv`. This derives the actual open-kernel
condition from the supplied topology and character.

`leftPhi_plus_compactOpenBasis` and
`leftPhi_stagesKernel_compactOpenBasis` explicitly expose the corresponding
compact-open bases. They install `T.topology`, `T.fieldT2`,
`isTopologicalRing_of_topologicalData F T`, and the supplied matrix-group
local compactness and nonarchimedean structure. Their local compactness
instances are derived from closed subgroups; none is a new premise.

`padic_leftPhiStagesCharacterEquiv` installs exactly those supplied
structures at rank `k+r+3`, and uses the just-derived open-kernel proof.
Its only representation premise is actual smoothness for `T.topology`.
Its source and target are the exact actions described above.
`padic_leftPhiStagesCharacterEquiv_natural` specializes the full naturality
equation with the same data. Exported result types and the localization
argument explicitly install the supplied topology and its Hausdorff
topological-ring data where required. There is no canonical-topology choice,
extra Haar condition, character-triviality condition or comparison premise.
The ambient inverse-half twist remains a later operation; no normalized
host comparison is asserted by these wrappers.

## Import and mathematical dependency audit

There are five direct project imports, listed as the first five names below:

```text
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHaar
Langlands.Representation.Induction.SplitStagesCharacterComparison
Langlands.Analysis.Local.QuotientMeasureExistence
Langlands.Group.GL.CompactOpen
```

The complete direct and transitive closure has 148 project modules,
excluding this entry. All 296 imported Lean/Markdown files are nonempty,
byte-identical to the published Library and verified against its manifest at
commit `6096ab5ac4bb214693970d29c770af26cb4cea48`.
No pending module or peer draft is imported. In particular, the separately
published source-action and normalized-section constructions are not inputs
to this unit.

The actual mathematical dependencies are the actual matrix groups,
projection/successor and closed subgroup calculations; actual nested
localization and section action; the proved actual full-intersection Haar
identity; continuous subtype equivalences; Haar measures and compatible
quotient-measure existence; the proved compact-open subgroup basis; and the
proved natural character-stages equivalence. Transitively, the latter uses
inverse-character twisting, ordinary coinvariant transport, compact-induction
transitivity and quotient integrals, their local inverse and kernel proofs,
and compact averaging for smooth modules. These are lower group, measure,
linear algebra and representation constructions. No derivative comparison,
segment conclusion or finiteness consumer supplies an input. Whittaker
modules in the closure provide algebraic group and character infrastructure,
without any coinvariant-finiteness conclusion.

| Condition | Actual dependency finding |
| --- | --- |
| Six host conclusions | The host statement and proof modules are absent from the closure. No mixed-minus compatibility or boundary conclusion supplies an input. The comparison proved here is the lower actual section comparison, with normalization and mixed-product assembly still separate. |
| Plus functors, adjunction and §4.13(d) | None supplies an input. The plus subgroup, projection and successor are elementary matrix constructions. |
| General Leibniz and derivative formulas | No Leibniz theorem, unproved BZ77 comparison, Ze80 §3.5 or §9.6 formula, or segment derivative formula is used. |
| Individual head and socle existence | Neither individual special-head/reverse-socle nor segment-socle/reverse-head existence supplies an input. |
| Linked and unlinked segment conclusions | No unlinked irreducibility, linked reverse-product structure, pair reducibility, juxtaposed reverse-product structure or reverse-product quotient homomorphism is used. |
| Segment products, commutation and gluing | No segment-socle product irreducibility, adjacent swap, two-segment commutation, linked-segment gluing, Ze80 4.2 or 9.7 criterion, or consequence is used. |
| Segment Jacquet formulas | No full, head, socle or special-exponent Jacquet formula, its successor or downstream conclusion supplies an input. |
| Special-head criterion and generic uniqueness | Neither special-head product irreducibility nor generic segment-product uniqueness is used. |
| Ordered existence, coverage and exhaustion | No ordered multisegment-socle or strong-head existence, socle or special-head exhaustion, quotient coverage or ordered conversion is used. |
| Analytic, tempered and square-integrable classification | No analytic segment classification, forward special essential square-integrability, tempered uniqueness, square-integrable Langlands classification, square-integrable or regular exhaustion, or Ze80 9.3 conclusion is used. |
| Two-supercuspidal consumers | Neither nonadjacent-product irreducibility, two-supercuspidal product structure nor its full-product assembly is used. No parent six-statement conclusion (b),(d),(e),(f) is used. |
| Supercuspidal and all-character finiteness | No supercuspidal, all-character single-block or arbitrary-character coinvariant-finiteness theorem or downstream consequence is used. |
| Other Whittaker finiteness | No irreducible or Levi-cuspidal coinvariant-finiteness conclusion or prohibited mirabolic finite-length route supplies an input. |
| Generality and normalization | All `k,r`, arbitrary supplied `T`, positive GL input rank and entire coefficient carriers are retained. Smoothness is the only representation premise. The actual Haar character is proved one; the ambient inverse-half normalization is explicitly reserved for subsequent assembly. |
| Published-input requirement | Every imported pair is published and unchanged. Prop-valued statement definitions, source formulas, drafts, pending constructions and consumer tasks provide no unproved comparison premise. The invoked generic comparison is a published proof. |
| Separate owners and controls | This unit constructs actual left character-stages comparison data; it does not duplicate the separate restriction-sequence or exactness work. Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and current suspensions remain binding. |

A scan of this module and its entire project closure finds no occurrence in
Lean code of the host's 38 excluded task identifiers or 24 named consumer
declarations, and no proof holes, new axioms or unsafe evaluation commands.
Excluded names in explanatory Markdown are audit prose. Development
compilation is distinct from independent semantic acceptance and publication.

## Complete project import closure

The following list contains every direct and transitive project import,
excluding this entry module. Mathlib is supplied by the pinned approved
environment and remains unchanged.

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
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedOrbitData
Langlands.Group.GL.MirabolicMixedOrbitRadicals
Langlands.Group.GL.MirabolicMixedOrbitSectionCoefficients
Langlands.Group.GL.MirabolicMixedOrbitSections
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
Langlands.HarmonicAnalysis.HaarConjugacy
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Compact.SurjectivityProof
Langlands.Representation.Compact.SurjectivityStatement
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHaar
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSection
Langlands.Representation.Dual.Definitions
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
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
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.LocalizationTransport
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Mirabolic.MixedProducts
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.ConjugationStabilizer
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.Nonarchimedean.Subgroup
```
