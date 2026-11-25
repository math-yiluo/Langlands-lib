# Natural character-localized compact induction in split stages

`Langlands.Induction.SplitStagesCharacterComparisonStatement` is a Prop-valued
`def`. It states a pairwise natural comparison with a prescribed quotient
integral. This file contains no proof of the comparison; the proof is
`Langlands.Induction.splitStagesCharacterComparison` in
`SplitStagesCharacterComparison`. Its entry module is
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
The Library's `notes/errata` has no errata file for that source.

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

## Dependency boundaries

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
consumers.
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

Only published results supply proved mathematical
inputs. The helper proves elementary interface properties; this statement
makes its proposition available but does not prove it. A citation or
conditional comparison is not a proof. The proof,
`splitStagesCharacterComparison`, retains the
complete exclusions. The six mixed-minus clauses of
`Derivative.MirabolicProductMinusCompatibilityStatement` remain separate.

## Complete project import closure

The following is the complete recursively computed project closure of the sole
direct import (101 modules, including the elementary integrand helper; the
present statement module is additional). All edges were checked against the
actual source. Its 100 modules other than the helper are those of Library
commit `7ad6e7323f2d14f5ccf8d30daa428878acda72c4`. Mathlib foundations are
pinned to Mathlib commit
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


## Independence audit against the excluded conditions

The checks in the following table cover the direct helper proof references
just listed and the complete transitive project closure of this statement. Every excluded family
includes its mathematical conclusion, the modules that prove it and downstream
consequences. A proposition definition, literature citation or
conditional comparison supplies no proved
input. The mathematical closure contains only the elementary constructions
and ordinary comparisons described above; the excluded consumer families do
not occur in it. In particular, incidental parabolic constructions are not
parabolic irreducibility/classification results.

| Exclusion condition | Direct and transitive dependency check |
| --- | --- |
| `SupercuspidalCoinvariantFinitenessStatement` (all-character single-block), every module proving it and every downstream consequence | Absent from the entire closure; no finite-dimensionality or finiteness input occurs. Missing general derivative or tensor inputs are not assumed from consumers. |
| `GenericSegmentProductUniqueness` | Absent from the closure and from all proof terms; no genericity or uniqueness result is used. |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible` | Neither these consumers nor the modules proving them or their consequences occur. The elementary quotient construction has no segment input. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom` and the modules that prove them | Absent throughout the closure; no socle product or quotient comparison is used. |
| `SegmentSocleProductIrreducibility` | Absent, including the modules that prove it and downstream consequences. |
| `AdjacentUnlinkedSegmentSocleSwap`; `TwoSegmentSocleCommutation` | No adjacent swap or segment commutation result is imported or invoked, directly or transitively. |
| `LinkedSegmentSocleGluing` | Absent throughout; no gluing statement is used. |
| `OrderedMultisegmentSocleExistence`; socle exhaustion | No existence or exhaustion theorem enters the construction. |
| Individual special-head/reverse-socle existence; individual segment-socle/reverse-head existence | Both families, the modules that prove them, and their consequences are absent. |
| Segment analytic classification; forward `SegmentSpecialEssentialSquareIntegrability` | No analytic, classification or square-integrability result appears anywhere in the closure. |
| Multisegment/special-head exhaustion; ordered strong/special-head existence; quotient coverage; ordered conversion | All four families, the modules that prove them and all of their downstream consequences are absent, directly and transitively. |
| Tempered/block uniqueness; `SquareIntegrableLanglandsClassification`; square-integrable exhaustion; regular exhaustion | No tempered, square-integrable, regular or classification input enters any dependency. |
| `SegmentHeadProductIrreducibility` | The special-head criterion, all of its conclusions, the modules that prove it and its transitive dependents are absent. |
| Every segment derivative formula, segment-socle/head existence or Jacquet formula, segment classification, and clauses (b), (d), (e), (f) of the six statements of `Classification.SegmentSocleDerivativesStatement` | None is imported, assumed, or used to prove a lower input. No general derivative theorem or clause (a)/(c) is used either; no unproved proposition is treated as proved. |
| `TwoSupercuspidalNonadjacentProductIrreducible`; `TwoSupercuspidalProductStructure` (full-product assembly) | No two-supercuspidal product result, module proving one, or downstream consequence enters the closure. |
| `SegmentFullJacquetFormula` and its proof `segmentFullJacquetFormula` (`Classification.SegmentFullJacquetProof`); `SegmentHeadJacquetFormula`; `SegmentSocleJacquetFormula`; `SegmentSpecialJacquetExponentNormFormula` | All four formula families and their mathematical consequences are absent. The generic algebraic module named `Jacquet.Coinvariants` contains only actual relation quotients and elementary maps, not any of these formulas. |
| Ze80 §§3.5, 9.6 derivative formulas; Ze80 4.2/9.7 irreducibility; Ze80 9.3 analytic/square-integrability; classification/exhaustion; the circular route from Ze80 4.2 through §2 to Proposition 1.11 | None is cited or used as proof evidence. No unproved BZ77 derivative assertion is assumed. |
| `IrreducibleCoinvariantFinitenessStatement`; `LeviCuspidalCoinvariantFinitenessStatement`; mirabolic finite-length route | These finiteness conclusions, the modules that prove them and downstream consequences are absent. No finite-length repair is used. |
| Shared lower derivative functors, derivative exactness, general Leibniz/support filtrations, geometric lemma, cuspidal support, representation finite length and plus-functor theorems | No such proved result is imported or used. The incidental structural exactness proposition and finite-length predicate are definitions only. `Tensor.Finite` is an elementary construction, not a consumer-derived tensor theorem or hypothesis. No matrix `plusSubgroup` specialization is needed. |
| Plus functors, adjunction, BZ77 §4.13(d) submodule detection, general Leibniz, arbitrary-character Whittaker finiteness and the six mixed-minus clauses of `Derivative.MirabolicProductMinusCompatibilityStatement` | No such conclusion is invoked or proved. Adjunction proposition definitions are incidental as explained above; no adjunction theorem is an input. Ordinary compact induction, actual stages, quotient integration and Haar covariance are present, with the prescribed Haar ratio, and are independently upstream of these consumers. Neither the helper nor this proposition proves any of those six comparison clauses. |


Mixed normalization, LeftPhi and the final assembly, and
Phi/Mackey/right-Phi/exactness and downstream E1, lie outside this statement;
these boundaries are not hypotheses or proof evidence. Compilation of this
statement or its presence in the Library does not prove the comparison;
`splitStagesCharacterComparison` does.
