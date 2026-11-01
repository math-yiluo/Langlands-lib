# Actual left-Phi host rank transports

Author: Worker 499.

This module constructs `leftPhiHostInductionIso` in
`Langlands.Derivative.MirabolicProductMinus`: the actual higher left mixed
product, followed by its published equality rank transport, is naturally
isomorphic to compact induction of its full smooth inducing coefficient in
ambient mixed-orbit coordinates. It also identifies the exact lower expected
host functor with explicit inverse-rank pullback of the lower mixed product,
and records the full representation and morphism formulas. These are internal
adapters toward BZ77 §4.13(b); the localized-product comparison and the host
LeftPhi compatibility remain separate obligations.

## Source and provenance

The original motivation is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, registered as `bernstein-zelevinsky-1977-induced-i`. The retained
original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8(b) and Proposition 1.9(f), printed pp.444–445 (one-based PDF
pages 5–6), give character localization, normalized normalizer actions and
induction comparisons. Sections 3.1–3.2, printed pp.450–451 (PDF pages
11–12), specify the mirabolic groups and minus functors. Section 4.12(II),
printed pp.456–457 (PDF pages 17–18), defines the left mixed product;
§4.13(b), printed p.458 (PDF page 19), states its natural compatibility.
Section 7.2, printed p.471 (PDF page 32), describes the two left orbit
representatives. These passages and relevant page images were read during
this task. The bounded supplied-source and public-note errata search found
no applicable BZ77 entry; no global absence is asserted.

The rank adapters, high coefficient functor and compact-induction natural
isomorphism are internal derived constructions. BZ77 does not literally
state the equality-cast interfaces used by this Library. Equality elimination
identifies a host rank cast with pullback by the inverse matrix rank map.
The high coefficient is the existing covariance-normalized mixed-product
coefficient pulled back along the actual inducing homomorphism. The published
`Induction.compactInducedTransport` supplies transport of the entire compact
function carrier. No new generic induction transport is constructed. The
published source coefficient definitions identify the lower expected
representation and its maps by reflexivity. No pending comparison or peer
draft supplies a proof body.

## Parameters and conventions

The p-adic part uses arbitrary `{p : ℕ} [Fact p.Prime]`,
`{F : PadicField.{uF} p}` and supplied `T : F.TopologicalData`, installing
exactly `T.topology` and its general-linear topological-group instances.
The high rank equivalence and membership identity need only a commutative
ring with a topology. All `k r : ℕ` are retained, including zero. The GL
factor has rank `k+1`; the high source is `mirabolic (r+1)`, namely
P_(r+2), and the low source is `mirabolic r`, namely P_(r+1). The high
ambient index is `k+r+2`, and the lower output index is `k+r+1`.
The lower minus functor is the actual `phiMinus T ψ r`, from P_(r+2) to
P_(r+1), for the supplied bundled continuous nontrivial unitary additive
character. There is no P_0.

The algebraic high transport, its evaluation formula, and its naturality
use independent coefficient universes `uV,uW,uV',uW'`. The smooth host
functors use the exact single input-carrier universe `uV` of the published
host target; compact induction raises the output carrier universe to
`max uF uV`. No universe saturation, finite-dimensional model, irreducible
input, admissibility hypothesis, selected vector or scalar omission is
introduced. The functor's coefficient is on the entire tensor product.

## Equality rank transport

`mirabolicRankCastMixedOrbitIso T h` compares the actual equality transport
`mirabolicRankCast T h` with continuous pullback by `(rankCast h).symm`.
After eliminating `h`, the component is the identity linear equivalence.
The inverse matrix rank cast at reflexive equality is proved to fix every
element by subtype, units and matrix extensionality. This gives the
intertwining law. Every naturality square is reflexive after equality
elimination. This proof checks the actual pullback direction rather than
assuming that an arbitrary carrier cast has the required group action.

## Full higher coefficient and compact induction

Write G = `mirabolic (k+r+2) F.Carrier`,
G' = `mirabolic (k+1+(r+1)) F.Carrier`,
H = `leftInducing k r F.Carrier` and
H' = `leftSubgroup (k+1) (r+1) F.Carrier`.
The continuous group equivalence `leftPhiHighRankEquiv` is the inverse
matrix rank cast for `totalRank_eq k r`. The exact identity
`leftPhiHighRank_mem_iff` says, for every g in G, that g belongs to H if
and only if its image belongs to H'. This is definitional from the actual
published subgroup construction.

For representations ρ of GL_(k+1) on V and τ of P_(r+2) on W,
`leftPhiHostInducingRepresentation` is

```text
A = (twist (T.leftCharacter (k+1) (r+1))
       (leftInducingRepresentation ρ τ)).comp (leftInducingHom k r).
```

This includes the entire upper-block covariance character. Its underlying
carrier is V ⊗[ℂ] W. `leftPhiHostInducingRepresentation_smooth` proves
smoothness from smoothness of both inputs by the published smooth tensor
coefficient theorem, open kernel of the actual character, and continuity
of the actual inducing homomorphism. The coefficient's restriction along
`stabilizerToInducing` for either of the two actual orbit representatives
is definitionally `leftPhiNormalizedStabilizer`; this is recorded in
`leftPhiHostInducingRepresentation_stabilizer` for every `i : Fin 2`.
It supplies no Mackey or localization comparison.

`leftPhiHostCompactInducedEquiv` specializes the published
`compactInducedTransport` to G,G',H,H', the exact membership identity and
the identity linear equivalence on V ⊗ W. Its source is compact induction
from H' of the original full twisted coefficient, pulled back by the
continuous high rank equivalence; its target is compact induction from H
of A. The required coefficient intertwining is reflexivity. Both sides
are the entire actual `CompactFunctions` carriers: covariant functions
with a single open right stabilizer and compact projected nonzero support.
The published generic theorem preserves these conditions in both directions
using open subgroup comaps, continuous quotient maps and compact images,
and intertwines actual right translation.

The forward evaluation formula is exactly

```text
E(z)(x) = z(leftPhiHighRankEquiv k r F.Carrier x).
```

`leftPhiHostInducingMap` is continuous inducing-hom pullback of the
actual covariance twist of the external tensor intertwiner, itself pulled
back along `leftProjection`. For every original compact function z and
arbitrary input intertwiners f and g across independent target carrier
universes, `leftPhiHostCompactInducedEquiv_natural` identifies E applied
after the actual source compact-induction map with the actual target
compact-induction map applied after E. Three subtype extensionality steps
and function extensionality reduce the equality to reflexivity at each
point. The equality therefore concerns every compact function, not a
spanning family or chosen representatives.

`leftPhiHostInducingFunctor` packages A and these tensor maps into the
actual smooth functor on both inputs. Tensor map identity and the published
`externalMap_comp` prove its functor laws. `leftPhiHostInductionIso`
first whiskers `mirabolicRankCastMixedOrbitIso` by the actual higher left
mixed-product functor, then uses the complete compact-induction equivalence
as each component. Its naturality is the preceding entire-function
naturality theorem. Its exact type is

```text
T.leftMixedProductFunctor (k+1) (r+1) ⋙ mirabolicRankCast T (totalRank_eq k r)
  ≅ leftPhiHostInducingFunctor T k r ⋙ SmoothRep.toRep ⋙
      compactInductionFunctor (leftInducing k r F.Carrier).
```

## Exact lower expected host formulas

`leftPhiExpectedPullback` applies the actual source `phiMinus T ψ r` in
the second factor, the actual lower normalized left mixed product, and
continuous pullback by `(rankCast (Nat.succ_add k r)).symm`. This is the
same direction as the lower equality rank transport in the unchanged
published `leftPhiExpected` functor.

`leftPhiExpectedHostIso` whiskers the rank-transport isomorphism by the
preceding actual source-Phi and product functors. Its full object
representation is compact induction from
`leftSubgroup (k+1) r F.Carrier` of
`leftPhiSourceCoefficient T k r ψ X.1.representation X.2`, followed by
that inverse-rank pullback. `leftPhiExpectedPullback_representation`
proves precisely this equality by reflexivity. The source coefficient
includes the full normalized source-Phi quotient and lower product
covariance; no residual scalar is discarded.

`leftPhiExpectedPullback_map` proves by reflexivity the full morphism
formula: pullback of the actual `compactInducedMap` of
`leftPhiSourceCoefficientMap` on the two supplied input maps. Thus this
adapter retains both natural input maps and the complete normalized
coefficient, without asserting that the higher localized product is
isomorphic to it.

## Import and mathematical dependency audit

The three direct project imports are

```text
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison
Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
```

The full project closure contains 98 imported modules, excluding this
entry. All 196 imported Lean/Markdown files are nonempty, byte-identical
to the published Library, and verified against its manifest at commit
`31d47a6f0dabd6dff6c65e1b78f4821ddedc9bc8`. Every imported pair is
published. The host proposition module supplies definitions only; its
comparison conclusions are not assumed. No pending stages, ambient
normalization or compact source-comparison unit is imported.

The direct mathematical inputs are actual equality and matrix rank casts,
the actual mixed-product subgroup and its covariance-normalized coefficient,
published smooth tensor/pullback/twist facts, the generic whole-carrier
compact-induction transport, and the actual source coefficient definitions.
Transitively these use elementary matrix and determinant identities,
character-localization and tensor-quotient algebra, continuous homomorphisms,
open subgroup comaps and compact support transport. Admissibility,
irreducibility, Noetherian and Whittaker infrastructure in the closure
supplies no finiteness hypothesis or consumer conclusion. The source
coefficient comparison is imported as a published interface, but none of
its comparison conclusions is needed for the high transport proof.

| Condition | Actual dependency finding |
| --- | --- |
| Six host conclusions | The unchanged host statement module supplies definitions and exact type targets only. No host comparison or boundary conclusion supplies an input. This unit proves high compact-induction and lower rank adapters. |
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
| Generality and normalization | All `k,r`, arbitrary supplied `T`, positive GL input rank and entire carriers are retained. The high smooth coefficient requires both original inputs smooth. The high algebraic transport and its naturality do not. Both higher covariance and the actual lower source-Phi normalization are retained. |
| Published-input requirement | Every imported pair is published and unchanged. Prop-valued statement definitions, source formulas, drafts, pending constructions and consumer tasks provide no unproved comparison premise. |
| Separate owners and controls | This host adapter unit does not duplicate the separate restriction-sequence or exactness work. Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and current suspensions remain binding. |
| Actual compact induction | Both complete covariant uniformly smooth compact-supported carriers are retained. Support transport and its inverse are proved in the published generic theorem. |
| Actual subgroup and rank map | The high subgroup membership equivalence is definitional for every ambient element. Both equality casts are compared with actual continuous inverse matrix-rank pullback, and the same maps occur in the full representation and morphism formulas. |


A scan of this module and its complete project closure finds no Lean-code
occurrence of the host's 38 excluded task identifiers or 24 named consumer
declarations, and no proof holes, new axioms or unsafe evaluation commands.
Excluded names in explanatory Markdown are audit prose. Development
compilation is separate from independent semantic acceptance and publication.

## Complete project import closure

Every direct and transitive project import, excluding this entry, is
listed below. The authorized environment supplies unchanged Lean and
Mathlib, pinned respectively to commits
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and
`5ed2965256430c3649e86755f9576b54eca72435`.

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
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
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDeterminant
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceAction
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison
Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
Langlands.Representation.Dual.Definitions
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.SplitKernelCharacterExtension
Langlands.Representation.Induction.SplitKernelLocalizationData
Langlands.Representation.Induction.SplitKernelSectionAction
Langlands.Representation.Induction.SplitQuotientProof
Langlands.Representation.Induction.SplitQuotientStatement
Langlands.Representation.Induction.SplitStagesRetraction
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
Langlands.Topology.Nonarchimedean.Subgroup
```

The complete external import boundary of these project modules is listed
below; its transitive standard-library imports are supplied by the pinned
environment, not project-authored mathematical inputs.

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.BigOperators.Fin
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
Mathlib.Data.Nat.Find
Mathlib.FieldTheory.Finite.Basic
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Measure.Haar.Basic
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
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.Nonarchimedean.Basic
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyConstant.Basic
```
