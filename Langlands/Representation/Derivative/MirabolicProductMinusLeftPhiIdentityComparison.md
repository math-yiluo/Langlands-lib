# Entire normalized left identity-orbit comparison

Author: Worker 499.

This module constructs `leftPhiIdentityNormalizedEquiv` and proves its full
naturality in `Langlands.Derivative.MirabolicProductMinus`. Positive-character
localization of the entire actual identity-orbit induction, including the
ambient inverse-half normalization, is representation-equivalent to the
actual lower left mixed-product induction with source Phi-minus, pulled back
along the proved continuous rank map. The comparison retains all localization
classes and compact functions and is natural in both inputs across independent
carrier universes.

This focused construction does not identify the higher mixed product with
its identity-orbit contribution. That step needs the separate natural Mackey
projection and ambient kernel comparison. It does not prove the six-part
`MirabolicProductMinusCompatibilityStatement` or the final host LeftPhi clause.

## Source and provenance

The original motivation is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, registered as `bernstein-zelevinsky-1977-induced-i`. The retained
original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8(b) and Proposition 1.9(f), printed pp.444–445 (one-based PDF
pages 5–6), define character localization, its normalized action, and
character-twist comparisons. Sections 3.1–3.2, printed pp.450–451 (PDF
pages 11–12), define the mirabolic minus functors. Section 4.12(II), printed
pp.456–457 (PDF pages 17–18), defines the left mixed product. Section
4.13(b), printed p.458 (PDF page 19), states its natural minus compatibility;
§7.2, printed p.471 (PDF page 32), describes its two orbit representatives.
These passages and relevant page images were read during this task. The
bounded supplied-source and public-note search found no applicable BZ77
errata entry; no global absence is asserted.

The present composition and smoothness specialization are internal derived
content. The original does not literally state these nested localization
interfaces. The module composes three published complete representation
equivalences: actual character stages, ambient induction normalization, and
normalized compact source comparison. It proves stabilizer smoothness by
continuous restriction of the actual twisted tensor coefficient. Naturality
is a composition of the three published full naturality equations. No peer
draft or unpublished candidate provides a proof input.

## Generality and rank conventions

All declarations quantify arbitrary `{p : ℕ} [Fact p.Prime]`,
`{F : PadicField.{uF} p}`, supplied `T : F.TopologicalData`, and
`k,r : ℕ`, including zero. The inputs to the equivalence are

```text
ρ : Representation ℂ GL_(k+1)(F) V, with IsSmooth ρ for T.topology,
ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology,
B : SmoothRep ℂ P_(r+2)(F).
```

The field, GL-carrier and mirabolic-carrier universes `uF,uV,uW` are
independent. Naturality allows independent target carrier universes
`uV',uW'`. No admissibility, irreducibility, finite dimension, finite length,
genericity, chosen vector, canonical topology, saturation or assumed
comparison premise is introduced. Smoothness is the only representation
condition; zero inputs and entire infinite-dimensional carriers are retained.
The unitary additive character already includes continuity and nontriviality.

The convention `mirabolic n F.Carrier = P_(n+1)(F)` gives higher product
rank `P_(k+r+3)`, source `P_(r+2)`, and output `P_(k+r+2)`. Source Phi-minus
is exactly `phiMinus T ψ r : P_(r+2) → P_(r+1)`; the ambient inverse-half
character is `phiMinusCharacter T (k+r+1)`. No `P_0` or Phi-minus on `P_1`
is introduced, including at `r=0`. The positive GL input remains `GL_(k+1)`.

Set

```text
G = plusSubgroup (k+r+1) F.Carrier,
L = mirabolic (k+r+1) F.Carrier,
p = plusProjection : G →* L,
s = plusSuccessor : L →* G,
H = leftStabilizer k r F.Carrier 1,
D = (leftStages k r F.Carrier 1).comap s,
θ = plusKernelTheta ψ (k+r+1),
χ = Mirabolic.phiMinusCharacter T (k+r+1),
σ = leftPhiNormalizedStabilizer T k r ρ B.representation 1,
C = leftPhiSourceCoefficient T k r ψ ρ B,
φ = leftPhiLowerRankEquiv k r F.Carrier.
```

The identity orbit is index `1`; index `0` is the cycle. The target rank of
`φ` is the actual `mirabolic (k+1+r) F.Carrier`. Its inverse matrix-rank cast
is retained in both the target representation and input-map formulas.

## Smoothness of the full stabilizer coefficient

`leftPhiNormalizedStabilizer_smooth` works for either orbit index and two
arbitrary smooth input representations. It rewrites the stabilizer action
as the restriction along `stabilizerToInducing` of the restriction along
`leftInducingHom` of

```text
twist (T.leftCharacter (k+1) (r+1)).toMonoidHom
  (leftInducingRepresentation ρ τ).
```

The full covariance scalar is
`ν_(k+1)^((r+2)/2) · ν_(r+2)^(-(k+1)/2)`. The published smooth tensor and
pullback theorem proves smoothness of `leftInducingRepresentation`.
`isSmooth_twist_iff` uses the actual character's proved open kernel.
`continuous_leftInducingHom` and `continuous_stabilizerToInducing` then give
the two smooth restrictions. Thus smoothness is derived for the entire
coefficient, with its covariance and actual stabilizer, without a new
smoothness premise on a quotient or a comparison theorem.

## Complete normalized representation equivalence

The source of `leftPhiIdentityNormalizedEquiv` is exactly

```text
twist χ (localizedAction p s θ (plusKernelTheta_sectionInvariant ψ (k+r+1))
  (compactInduced H σ)).
```

Its carrier is the complete character quotient of `CompactFunctions H σ`
by all relations `π(u)z − θ(u) • z`, for the actual kernel `p.ker`. The
action uses the actual successor section and the full determinant
inverse-half twist `χ`. It is not restricted to a set of generators,
selected functions, selected support or a subrepresentation.

First, `padic_leftPhiStagesCharacterEquiv T ψ k r 1 σ` applies to the
just-proved smooth coefficient. This published equivalence identifies the
entire unnormalized localization with compact induction on `D` of the actual
nested section quotient. Its actual quotient measure and Haar data come
from the supplied topology and actual groups, with the entire stages Haar
character proved one. `twistEquiv χ` keeps its full underlying linear
equivalence while twisting both actions by the ambient normalization.

Second, `leftPhiAmbientInductionEquiv` moves this full ambient character
into the actual induced coefficient. Its function map multiplies each
value at `l : L` by `χ(l)`. Third, `leftPhiCompactSourceEquiv` transports the
entire normalized identity coefficient into the actual source-Phi
coefficient `C` and transports compact functions along `φ`. Thus the exact
target representation is

```text
(compactInduced (leftSubgroup (k+1) r F.Carrier) C).comp φ.toMonoidHom.
```

Here `C` acts on `V ⊗[ℂ] ((Mirabolic.phiMinus T ψ r).obj B)` with both the
actual normalized source-Phi action and lower positive covariance
`T.leftCharacter (k+1) r`. The published source coefficient equivalence
sends every tensor class `[v ⊗ w]` to
`v ⊗ Mirabolic.phiMinusQuotient T ψ r B w`. The compact transport preserves
covariance, one uniform open right stabilizer, compact projected support,
and right-translation equivariance in both directions. No remaining scalar
or character equality is assumed by this composition.

The definition is precisely the transitive composition of those three
representation equivalences, so its inverse and bijectivity hold on the
full carriers. All topology and topological-group instances in the public
type come from `T`, at the actual required ranks.

## Naturality on every localization class

For arbitrary `f : ρ.IntertwiningMap ρ'` and
`g : B.representation.IntertwiningMap B'.representation`, write

```text
m = leftPhiNormalizedStabilizerMap T k r ρ B.representation f g 1,
n = leftPhiSourceCoefficientMap T k r ψ ρ B f g,
E = leftPhiIdentityNormalizedEquiv T k r ρ ψ B hρ.
```

The source map is the actual `sectionMap` of `compactInducedMap H m`,
with the ambient `twistIntertwining χ`. The target map is exactly
`pullbackMap φ.toMonoidHom (compactInducedMap (leftSubgroup (k+1) r F.Carrier) n)`.
`leftPhiIdentityNormalizedEquiv_natural` proves that these maps commute with
`E` on every localization element `z`, across four independent coefficient
universes.

The proof exposes the threefold composition and removes only the underlying
function wrappers for `twistEquiv`, `twistIntertwining` and `pullbackMap`.
Two private application lemmas are reflexivity proofs of the unchanged
underlying maps. It instantiates the published stages naturality with the
full actual coefficient map and both proved smoothness instances. Applying
the target ambient and compact equivalences to that equality gives the
first step. The explicitly instantiated ambient naturality equation gives
the second step, and the explicitly instantiated compact source naturality
equation gives the third. `congrArg` and equality transitivity compose them.
The final `with_reducible exact` checks the same equality without unfolding
the published measure/comparison constructions. This is ordinary kernel
checked equality; it adds no assumption or evaluation mechanism.

## Import and mathematical dependency audit

The three direct imports are

```text
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiStagesComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiInductionNormalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCompactComparison
```

The full project closure contains 169 imported modules, excluding this
entry. All 338 imported Lean/Markdown files are nonempty, byte-identical to
the published Library and checked against its manifest at commit
`1741653e5f4f861282ff64d062269adbcc65c686`. No pending module is imported.
In particular the separate host transport, ambient Phi kernel comparison
and natural Mackey projection candidates provide no proof input.

The actual direct mathematical dependencies are smooth twisted tensor
restriction, the full actual positive-character stages equivalence and its
naturality, the actual compact-induction character transport and its
naturality, and the full normalized compact source comparison and its
naturality. Transitively these use explicit matrix subgroup and determinant
identities, character relation-span quotients and tensor quotient transport,
actual compatible Haar quotient measures, compact-open bases, the proved
ordinary split-stages comparison and its local inverse/kernel proofs,
compact-induction transitivity, compact averaging and source-minus
smoothness. Imported admissibility, irreducibility, finite-length and
Whittaker infrastructure supplies no representation finiteness premise or
consumer conclusion. The compact quotient/local-section results are lower
induction constructions, not Whittaker coinvariant finiteness.

| Condition | Actual dependency finding |
| --- | --- |
| Six host conclusions | The host statement and proof modules are absent. No mixed-minus compatibility or boundary conclusion supplies an input. This unit composes the full normalized identity-orbit comparison with its actual rank pullback. The higher mixed product and natural Mackey projection remain separate. |
| Plus functors, adjunction and §4.13(d) | None supplies an input. The plus subgroup, projection and successor are elementary matrix constructions. |
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
| Generality and normalization | All `k,r`, arbitrary supplied `T`, positive GL input rank and entire carriers are retained. Both input representations are smooth, with no additional representation hypothesis. Both the ambient inverse-half character and the lower source normalization are present in the compared actions. |
| Published-input requirement | Every imported pair is published and unchanged. Prop-valued statement definitions, source formulas, drafts, pending constructions and consumer tasks provide no unproved comparison premise. |
| Separate owners and controls | This composition does not duplicate the separate restriction-sequence or exactness work. Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and current suspensions remain binding. |
| Actual compact induction | Both complete covariant uniformly smooth compact-supported carriers are retained. Support transport and its inverse are proved in the published generic theorem. |
| Actual subgroup and rank map | The exact subgroup membership equivalence is proved for every ambient element. The continuous inverse rank cast is present in the target action and the evaluation formula. |

A scan of this entry and its complete project closure finds no Lean-code
occurrence of the host's 38 excluded task identifiers or 24 named consumer
declarations, and no proof holes, new axioms or unsafe evaluation commands.
Excluded names in explanatory Markdown are audit prose. The dependency
inspection above supports the mathematical exclusions in addition to the
symbol scan. Compilation and declaration inspection are separate from
independent semantic acceptance and publication.

## Complete project import closure

Every direct and transitive project import, excluding this entry, is listed
below. The authorized environment supplies unchanged Lean and Mathlib,
pinned respectively to commits
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
Langlands.Representation.Category.Twist
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Compact.SurjectivityProof
Langlands.Representation.Compact.SurjectivityStatement
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDeterminant
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCompactComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHaar
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiInductionNormalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceAction
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiStagesComparison
Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
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
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
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
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Products.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.Data.Fin.Rev
Mathlib.Data.Matrix.Block
Mathlib.FieldTheory.Finite.Basic
Mathlib.GroupTheory.Coset.Defs
Mathlib.GroupTheory.DoubleCoset
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.GroupTheory.GroupAction.Quotient
Mathlib.GroupTheory.Subgroup.Centralizer
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
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.Valuation.Integral
Mathlib.Tactic.Linarith
Mathlib.Tactic.NoncommRing
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Pointwise
Mathlib.Topology.Algebra.Group.Quotient
Mathlib.Topology.Algebra.Group.Subgroup
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.Nonarchimedean.Basic
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.ProperAction.Basic
Mathlib.Topology.Algebra.Support
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Compactness.LocallyCompact
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.ContinuousMap.CompactlySupported
Mathlib.Topology.Homeomorph.Quotient
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyConstant.Basic
Mathlib.Topology.Order.Compact
Mathlib.Topology.UrysohnsLemma
```
