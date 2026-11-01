# Natural character-localized compact induction in split stages

`Langlands.Induction.SplitStagesCharacterComparisonStatement` is a Prop-valued
`def`. It states a pairwise natural comparison with a prescribed quotient
integral. This file contains no proof of the comparison. Its entry module is
`Langlands.Representation.Induction.SplitStagesCharacterComparisonStatement`.
The sole direct project import is the elementary interface module
`Langlands.Representation.Induction.SplitStagesCharacterIntegrand`.

## Derived provenance

This is an internal derived compact-induction/localization comparison target, rather
than a literal theorem of Bernstein and Zelevinsky. The registered original is
`bernstein-zelevinsky-1977-induced-i`, *Induced representations of reductive
p-adic groups I* (1977), retained at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
No errata file for that source was present in the current Library or project
notes at the time of this audit.

BZ77 §1.7–1.8, printed p.444 (PDF p.5), fixes the Haar change of variables,
right-translation compact induction and character relation quotient. Sections
3.1–3.2, printed pp.450–451 (PDF pp.11–12), introduce the mirabolic split-group
applications; their plus-functor and adjunction assertions are not proof inputs
here. Proposition 4.13(b,c), printed p.458 (PDF p.19), and §7.2, printed p.471
(PDF p.32), motivate later natural comparisons. Those paragraphs do not state
this arbitrary-group result. The integral in §5.17, printed p.466 (PDF p.27),
uses the inverse character before passage to the coefficient quotient. It
explains the inverse weight used below. None of those source assertions is
assumed as an unproved Lean comparison. The elementary integrand proofs use the
published relation-quotient, compact-slice and simple-function constructions. The present definition
asserts the additional comparison and naturality as a proposition to be proved.

## Quantifiers and assumptions

The definition has independent universe parameters `uG,uL,uV,uW`; the entire
assertion, including its groups and coefficient modules, lies inside `Prop`.
It quantifies over `G : Type uG` with a group, topology, topological group,
Hausdorff and local compactness structure; `L : Type uL` has just a group,
topology and topological group structure. These are exactly the group
assumptions of the published `splitStagesCompactEquiv`.

The actual continuous homomorphisms `r : G →* L` and `s : L →* G` satisfy
`hrs : ∀ l, r (s l) = l`. The subgroups `P,H` are closed, with `r.ker ≤ P`
and `H ≤ P`. The only section-containment hypothesis is
`hsH : ∀ l : P.comap s, s (l : L) ∈ H`: it concerns the section over that
subgroup, without restricting the section elsewhere. The arbitrary
`theta : SmoothCharacter ℂ r.ker` supplies its actual open kernel, and the
only supplied character-invariance hypothesis is
`SplitKernelLocalization.SectionInvariant r s theta.toMonoidHom`.

Using the actual retraction `rP` specified below, all of the following are
quantified, retaining the ordinary comparison's assumptions without imposing
an additional normalization:

- A local compactness structure on `rP.ker`.
- Measurable spaces and Borel-space instances on `rP.ker`,
  `I = (H.subgroupOf P).comap rP.ker.subtype`, and `LeftQuotient I`.
- A supplied measure `nu` on `LeftQuotient I`, finite on compact sets.
- Supplied regular Haar measures `muN` on `rP.ker` and `muI` on `I`, both left
  Haar and right invariant, together with `IsCompatible I muN muI nu`.
- Closedness of `r.ker` in `G` and compact-open subgroup neighborhood bases
  at one in `G` and in `rP.ker`.

The explicit forall binders retain compatibility, closedness and both bases
even though those assumptions are not needed merely to form the equation.
Their underscore-prefixed names in Lean do not remove any hypothesis.

Finally `V : Type uV` and `W : Type uW` have arbitrary additive commutative
group and complex-module structures. The representations `sigma` and `tau`
of `H` are arbitrary and smooth. Zero modules are included. There is no
admissibility, irreducibility, finite dimension, finite length, nonzero-vector,
compact-group, discrete-group, finite-index or character-triviality condition.
There is no universe-saturation constraint or theorem-valued comparison
premise. In particular `uV` and `uW` need not agree with each other or with
either group universe.

## Actual coefficient carrier and action

The proposition uses the following concrete data, named by let bindings or
expanded in its actual representations:

```text
K       = P.comap s
rP      = splitStagesRetraction r s hrs P hker
sP      = s.subgroupComap P
HP      = H.subgroupOf P
phi     = (Subgroup.subgroupOfEquivOfLe hHP).toMonoidHom
sigmaP  = sigma.comp phi
tauP    = tau.comp phi
thetaP  = theta.toMonoidHom.comp
            (splitStagesKernelEquiv r s hrs P hker).toMonoidHom
A       = SplitKernelLocalization.kernelIntersection rP HP
eta     = SplitKernelLocalization.intersectionCharacter rP thetaP HP
C_sigma = Jacquet.Localization.Coinvariants sigmaP A eta
C_tau   = Jacquet.Localization.Coinvariants tauP A eta.
```

The proposition obtains `thetaP` from `SplitStagesCharacter.kernelCharacter`,
whose monoid homomorphism is exactly the displayed composite and whose open
kernel is derived by continuous preimage. It uses the proved
`SplitStagesCharacter.sectionInvariant` to derive the nested invariance from
the ambient one, `section_mem` to derive `hsHP : ∀ l : K, sP l ∈ HP` from
`hsH`, and `subgroup_closed` for the actual closed preimage of `H` under
`P.subtype`. These are constructed proofs, not extra assumptions.

For each coefficient representation let

```text
lambda_sigma = SplitKernelLocalization.subgroupAction
                 rP sP thetaP derivedInvariance HP hsHP sigmaP
chi = Jacquet.complexCharacter
        (splitKernelHaarRatio rP sP HP hsHP hHPclosed)
kappa_sigma = twist chi lambda_sigma.
```

The same formula with `tauP` defines `kappa_tau`. These representations act
on exactly `C_sigma` and `C_tau`. For inverse section conjugation
`alpha(l)(n) = sP(l)⁻¹ * n * sP(l)`, the existing Haar ratio is
`mulEquivHaarChar(alpha(l)|I) / mulEquivHaarChar(alpha(l))`. It is the
subgroup-to-kernel ratio for forward precomposition with that inverse
conjugation; it is not inverted. There is no hidden scalar or residual
extension twist. The integrand helper's proved `coefficientAction_mk` states
on actual quotient classes

```text
kappa_sigma l [v] = (chi l : ℂ) •
  [sigmaP (SplitKernelLocalization.subgroupSection sP HP hsHP l) v].
```

This proposition introduces no quotient-carrier replacement or additional
intersection transport. The helper's sole group intersection equivalence
preserves the underlying group element and only exchanges membership proofs.

## Canonical evaluation and pairwise naturality

For each coefficient representation define the actual source and target

```text
Source_sigma = SplitKernelLocalization.localizedAction r s
                 theta.toMonoidHom htheta (compactInduced H sigma)
Target_sigma = compactInduced K kappa_sigma.
```

For every pair `sigma,tau`, the proposition first chooses
`E_sigma : Representation.Equiv Source_sigma Target_sigma` and
`E_tau : Representation.Equiv Source_tau Target_tau`. Only after both choices
does it quantify over all intertwiners `T : sigma.IntertwiningMap tau`.
Thus the choices cannot depend on `T`; naturality includes arbitrary maps
between independent carrier universes. No global universe-saturated family
is introduced.

The first two conjuncts require the integral evaluation formula for each
chosen equivalence. For `sigma`, every `f : CompactFunctions H sigma` and
`l : L` satisfies

```text
eval K kappa_sigma
  (E_sigma (Jacquet.Localization.mk (compactInduced H sigma)
    r.ker theta.toMonoidHom f)).val l
  = AlgebraicIntegral.integral nu (S_sigma f l).
```

Here `S_sigma f l` is exactly `SplitStagesCharacter.integrand ... f l`, the
canonical `SimpleFunc` constructed by `compactlySupportedSimpleFunc`. The
proved `SplitStagesCharacter.integrand_mk` gives, for every `n : rP.ker`,

```text
S_sigma f l (quotientMap I n)
  = Jacquet.Localization.mk sigmaP A eta
      (((thetaP n)⁻¹ : ℂˣ) • eval H sigma f.val (((n : P) : G) * s l)).
```

Unit scalar multiplication uses its complex value; the weight is the inverse
character. It is not a free integrand. The helper proves left-`I` invariance
by cancelling the inverse character with the localized covariance relation,
descends through `QuotientIntegration.descend`, and proves local constancy
using the smooth character and compact-function local constancy. Its support
is contained in the actual compact closed quotient support of
`splitStagesKernelSlice`; localization may shrink that support. It then
packages the function with `compactlySupportedSimpleFunc` and proves
finite-measure support for measures finite on compact sets. The paired helper
Markdown explains the implemented proofs in detail. The `tau` conjunct uses
the same construction on the actual carrier `W`.

The last conjunct requires, for every `T` and every actual localized source
class `z`,

```text
E_tau (SplitKernelLocalization.sectionMap r s theta.toMonoidHom htheta
  (compactInducedMap H T) z)
  = compactInducedMap K
      (twistIntertwining chi
        (SplitKernelLocalization.subgroupMap rP sP thetaP derivedInvariance
          HP hsHP (restrictAlongMap phi T)))
      (E_sigma z).
```

These are the actual source and target maps. `restrictAlongMap phi T` keeps
`T` as its linear map, `subgroupMap` sends `[v]` to `[T v]`, and
`twistIntertwining chi` preserves that linear map with the stated Haar twist.
Postcomposition by it is exactly `compactInducedMap K`. On the source,
`sectionMap` is the actual descended localization map of
`compactInducedMap H T`, sending `[f]` to `[T ∘ f]`. The naturality equation
therefore refers to the prescribed coefficient quotient maps, without a
hidden abstract natural transformation.

## Dependency and acceptance boundaries

The present module defines a proposition and proves no comparison. Its only
direct import supplies the coefficient and canonical integrand. Those
helper proofs use `Jacquet.Localization.mk_apply_subgroup`, actual kernel and
intersection maps, the compact slice, quotient descent/openness, and
`compactlySupportedSimpleFunc` with its finite-measure-support lemma. The
slice's mathematical route is `compactStagesEquiv` followed by
`splitKernelCompactEquiv`, using the actual compact function, its open
stabilizers and compact quotient support. The ordinary
`splitStagesCompactEquiv` is imported in that helper's module for its data
and established conventions; the new character comparison is not inferred
from it inside this definition.

The complete transitive closure additionally loads ordinary relative-integral,
compact averaging, normal-coinvariant kernel and induction-in-stages proofs.
Their group, measure and linear-algebra inputs are upstream of the excluded
consumers. The audited current status of
`compactInductionNormalCoinvariantKernel` is a published proof; see
`notes/audits/external-library-2026-10-29/induction-whittaker-smooth.md`, P3-089.

`Induction.StructuralStatement` is incidentally imported by
`CompactQuotientProof`; it defines Prop-valued smooth Frobenius, induction
exactness and open-subgroup adjunction clauses. No proof of those clauses is
loaded or used, and the closure references those names only in that module
and its import. `Category.Basic` imports Mathlib finite-length predicate
infrastructure and defines `HasFiniteLength`, but no representation
finite-length theorem enters this construction. The elementary
`Tensor.Finite`, block/parabolic, inverse-transpose and local-field
normalization modules are incidental through
`CompactAutomorphismIntegralProof → CompactAutomorphism → InverseTranspose`.
They supply elementary tensor construction/smoothness, matrix and modulus
facts, without segment tensor, derivative, irreducibility or classification
conclusions. The audit below distinguishes these actual imports from proof
inputs. It does not claim that parabolic or ordinary Haar/stages modules are
absent.

Only independently accepted and published results supply proved mathematical
inputs. The helper proves elementary interface properties; this statement's
independent acceptance and publication will make its proposition available,
not prove it. A citation, draft, conditional comparison, pending proof or
ownership message is not a proof. The exact proof successor is arranged only
after independent acceptance and publication of this statement, retaining the
complete inherited exclusions. The host's six mixed-minus clauses remain
separate.

## Complete project import closure

The following is the complete recursively computed project closure of the sole
direct import (101 modules, including the elementary integrand helper; the
present statement module is additional). All edges were checked against the
actual source. Its 100 already-published modules are byte-identical to Library
base `7ad6e7323f2d14f5ccf8d30daa428878acda72c4`; the remaining module is the
separately staged helper. Mathlib foundations are pinned by environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. Statement definitions in this list
are not evidence that their propositions are true.

```text
Langlands.Analysis.Local.QuotientAutomorphismProof
Langlands.Analysis.Local.QuotientAutomorphismStatement
Langlands.Analysis.Local.QuotientAverageReal
Langlands.Analysis.Local.QuotientMass
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientMeasurePrerequisites
Langlands.Analysis.Local.QuotientPositiveLifting
Langlands.Analysis.Local.QuotientTopology
Langlands.Analysis.Local.SplitKernelQuotient
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Maps
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.PadicOppositeBlocks
Langlands.Group.GL.ReverseBlocks
Langlands.Group.HaarModulus
Langlands.HarmonicAnalysis.AlgebraicIntegral
Langlands.HarmonicAnalysis.AlgebraicIntegrand
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
Langlands.Representation.Induction.BlockFactors
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
Langlands.Representation.Induction.SplitKernelIntegral
Langlands.Representation.Induction.SplitKernelLocalizationData
Langlands.Representation.Induction.SplitKernelSectionAction
Langlands.Representation.Induction.SplitQuotientProof
Langlands.Representation.Induction.SplitQuotientStatement
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
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.ConjugationStabilizer
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.Nonarchimedean.Subgroup
```


## Independence audit against inherited conditions

The checks in the following table cover the direct helper proof references
just listed and the complete transitive project closure of this statement. Every excluded family
includes its mathematical conclusion, exact proof successors and downstream
consequences. A proposition definition, literature citation, private draft,
conditional comparison, pending proof or ownership message supplies no proved
input. The mathematical closure contains only the elementary constructions
and ordinary comparisons described above; the excluded consumer families do
not occur in it. In particular, incidental parabolic constructions are not
parabolic irreducibility/classification results.

| Inherited exclusion condition | Direct and transitive dependency check |
| --- | --- |
| `SupercuspidalCoinvariantFinitenessStatement`, all-character single-block task `62de5903-b616-4b5c-88eb-a066b77c5467`, and every successor/downstream consequence | Absent from the entire closure; no finite-dimensionality or finiteness input occurs. Missing general derivative or tensor inputs are not assumed from consumers. |
| `GenericSegmentProductUniqueness`, task `30341ae4-65f2-4a0e-9283-763db01a409e` | Absent from the closure and from all proof terms; no genericity or uniqueness result is used. |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`; tasks `23e98d90-6055-4e35-91a9-b0f5d8a84961`, `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`, `8fa9f68b-fa1b-431a-97f6-5b163964d1fc` | Neither these consumers nor their successors or consequences occur. The elementary quotient construction has no segment input. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom`, task `7ff2a1e9-89dc-439e-a861-a567b3db92bf` and proof successors | Absent throughout the closure; no socle product or quotient comparison is used. |
| `SegmentSocleProductIrreducibility`, task `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | Absent, including successors and downstream consequences. |
| `AdjacentUnlinkedSegmentSocleSwap`, tasks `e3634665-571b-4852-9f4c-bab8a1053434`, `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`; `TwoSegmentSocleCommutation`, tasks `426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0` | No adjacent swap or segment commutation result is imported or invoked, directly or transitively. |
| `LinkedSegmentSocleGluing`, tasks `c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea` | Absent throughout; no gluing statement is used. |
| `OrderedMultisegmentSocleExistence`, task `23189526-80b0-4828-a6d4-7ebec2cbeef5`; socle exhaustion `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | No existence or exhaustion theorem enters the construction. |
| Individual special-head/reverse-socle existence `67279e36-f3c2-42e3-9302-11729784042e`; individual segment-socle/reverse-head existence `4ca79bbd-589e-476b-9f65-661e799984b5` | Both families, their successors, and their consequences are absent. |
| Segment analytic classification `aca8805b-054f-4d56-8045-12db7f623404`; forward `SegmentSpecialEssentialSquareIntegrability`, task `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | No analytic, classification or square-integrability result appears anywhere in the closure. |
| Multisegment/special-head exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`; ordered strong/special-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`; quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`; ordered conversion `8252833d-c269-41a9-824c-5879e531b23b` | All four families and all of their successors/downstream consequences are absent, directly and transitively. |
| Tempered/block uniqueness `52e97845-36bb-457d-b76f-70753334b88c`; `SquareIntegrableLanglandsClassification`, task `1cb45da2-7007-4351-a694-594fb148b8d1`; square-integrable exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4`; regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac` | No tempered, square-integrable, regular or classification input enters any dependency. |
| `SegmentHeadProductIrreducibility`, task `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | The special-head criterion and all of its conclusions/successors/transitive dependents are absent. |
| Every segment derivative formula, segment-socle/head existence or Jacquet formula, segment classification, and clauses (b), (d), (e), (f) of the parent six-statement contribution | None is imported, assumed, or used to prove a lower input. No general derivative theorem or clause (a)/(c) is used either; no pending proposition is treated as proved. |
| `TwoSupercuspidalNonadjacentProductIrreducible`, task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`; `TwoSupercuspidalProductStructure`, full-product assembly `ab61f565-1427-4746-ba77-46097563e962` | No two-supercuspidal product result, successor, or downstream consequence enters the closure. |
| `SegmentFullJacquetFormula`, arrangement `ed48ae06-964c-4c84-9e62-978f5a953ca7` and exact proof successor; `SegmentHeadJacquetFormula`, task `55ad1e10-62d8-46b7-a081-909ef0056426`; `SegmentSocleJacquetFormula`, task `b95105c6-f8bb-4641-ae53-2f49d1e7f034`; `SegmentSpecialJacquetExponentNormFormula`, task `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | All four formula families and their mathematical consequences are absent. The generic algebraic module named `Jacquet.Coinvariants` contains only actual relation quotients and elementary maps, not any of these formulas. |
| Ze80 §§3.5, 9.6 derivative formulas; Ze80 4.2/9.7 irreducibility; Ze80 9.3 analytic/square-integrability; classification/exhaustion; the circular route from Ze80 4.2 through §2 to Proposition 1.11 | None is cited or used as proof evidence. No unproved BZ77 derivative assertion is assumed. |
| `IrreducibleCoinvariantFinitenessStatement`, task `5ab445dc-d2b4-4072-80d1-6370870a4a26`; `LeviCuspidalCoinvariantFinitenessStatement`, task `3ff5c8fb-397c-4345-bcb3-5d98a0993d18`; mirabolic finite-length route `5428fe2c-013c-482d-aa6e-7df43e7191aa` | These finiteness conclusions, proof successors and downstream consequences are absent. No finite-length repair, pending or otherwise, is used. |
| Shared lower derivative functors, derivative exactness, general Leibniz/support filtrations, geometric lemma, cuspidal support, representation finite length and plus-functor theorems | No such proved result is imported or used. The incidental structural exactness proposition and finite-length predicate are definitions only. `Tensor.Finite` is an elementary construction, not a consumer-derived tensor theorem or hypothesis. No matrix `plusSubgroup` specialization is needed. |
| Plus functors, adjunction, BZ77 §4.13(d) submodule detection, general Leibniz, arbitrary-character Whittaker finiteness and the six host mixed-minus clauses | No such conclusion is invoked or proved. Adjunction proposition definitions are incidental as explained above; no adjunction theorem is an input. Ordinary compact induction, actual stages, quotient integration and Haar covariance are present, with the prescribed Haar ratio, and are independently upstream of these consumers. Neither the helper nor this proposition proves any of the six host comparison clauses. |


Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and all
other operator suspensions remain binding. No paused worker is contacted or
awakened to execute this work. Worker 499 retains mixed normalization,
LeftPhi and final assembly; Worker 837 retains Phi/Mackey/right-Phi/exactness
and downstream E1. These ownership facts are coordination boundaries, not
hypotheses or proof evidence. The comparison statement and its proof must
receive their own independent acceptance and publication; compilation, statement acceptance or publication does not prove that comparison.
