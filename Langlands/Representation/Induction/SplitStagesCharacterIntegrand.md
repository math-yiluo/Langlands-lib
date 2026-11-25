# Canonical character-localized split-stages integrand

This module supplies the actual coefficient action and the canonical descended
simple function for the character-localized split-stages comparison. It proves
elementary descent and regularity facts. It does not construct or assert a
comparison equivalence. All declarations are in
`Langlands.Induction.SplitStagesCharacter`.

## Derived provenance

This is internal derived compact-induction/localization interface data, rather
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
assumed as an unproved Lean comparison. The proofs here instead use the
published relation-quotient, compact-slice and simple-function constructions.

## Actual coefficient data

The independent group universes are `uG,uL`; the coefficient module has its own
universe `uV`. Let `G` be a Hausdorff locally compact topological group, let `L`
be a topological group, and let `r : G →* L`, `s : L →* G` be continuous with
`r (s l) = l`. For closed subgroups `H ≤ P ≤ G` containing `r.ker` in `P`, put

```text
K      = P.comap s
rP     = splitStagesRetraction r s hrs P hker
sP     = s.subgroupComap P
HP     = H.subgroupOf P
phi    = (Subgroup.subgroupOfEquivOfLe hHP).toMonoidHom
sigmaP = sigma.comp phi
I      = HP.comap rP.ker.subtype
A      = SplitKernelLocalization.kernelIntersection rP HP
eta    = SplitKernelLocalization.intersectionCharacter rP thetaP HP
C      = Jacquet.Localization.Coinvariants sigmaP A eta.
```

Only `hsH : ∀ l : K, s (l : L) ∈ H` is supplied. `section_mem` derives the
corresponding membership in `HP`, and `subgroup_closed` is the preimage of the
closed set `H` under `P.subtype`. There is no containment requirement on the
section outside `K`.

For an arbitrary `theta : SmoothCharacter ℂ r.ker`, `kernelCharacter` pulls
back its monoid homomorphism and its open kernel through the actual continuous
kernel equivalence `splitStagesKernelContinuousEquiv`. Thus
`thetaP = theta.toMonoidHom.comp (splitStagesKernelEquiv ...).toMonoidHom`.
`sectionInvariant` derives the nested section invariance from the supplied
ambient `SplitKernelLocalization.SectionInvariant r s theta.toMonoidHom` by
applying it to the same underlying group elements. This is a proof, not an
additional nested invariance hypothesis.

With the local compactness and measurable/Borel structures on `rP.ker` and `I`
used by the published ordinary comparison, `haarCharacter` is exactly

```text
chi = Jacquet.complexCharacter
  (splitKernelHaarRatio rP sP HP section_mem subgroup_closed).
```

For inverse section conjugation `alpha(l)(n) = sP(l)⁻¹ * n * sP(l)`, that
existing ratio is `mulEquivHaarChar(alpha(l)|I) / mulEquivHaarChar(alpha(l))`.
Closedness supplies local compactness of `I`. The ratio uses forward
precomposition Haar scaling and then the existing complex-character map;
it is not inverted. `coefficientAction` is the actual representation

```text
kappa = twist chi
  (SplitKernelLocalization.subgroupAction
    rP sP thetaP sectionInvariant HP section_mem sigmaP)
```

on exactly `C`. The proved `coefficientAction_mk` gives, on every representative,

```text
kappa l [v] = (chi l : ℂ) • [sigmaP (subgroupSection sP HP section_mem l) v].
```

There is no residual extension twist or scalar choice. The intersection
character can be nontrivial. No abstract isomorphic replacement carrier is
introduced. The only intersection equivalence used in the descent proof is
the published `intersectionEquiv rP HP`: it exchanges membership proofs and
preserves the underlying group element. There is no newly defined quotient
transport concealing representative behavior.

## Canonical function and implemented proofs

For `f : CompactFunctions H sigma` and `l : L`, `kernelFunction` is

```text
n ↦ Jacquet.Localization.mk sigmaP A eta
      (((thetaP n)⁻¹ : ℂˣ) • eval H sigma f.val (((n : P) : G) * s l)).
```

Units act through their complex values. For `i : I`, use
`a = (intersectionEquiv rP HP).symm i : A`. The original function covariance
contributes `sigmaP a`, and `mk_apply_subgroup` turns it into multiplication
by `eta a = thetaP i`. The inverse factor at `i*n` then cancels this factor.
`kernelFunction_left_mul` proves the resulting equality before descent.
`integrandFunction` uses `QuotientIntegration.descend I` with that proof;
`integrandFunction_mk` proves its value on every `quotientMap I n` is precisely
the displayed expression. The convention is the actual left quotient `I\rP.ker`.

The private local-constancy lemma uses the open kernel of `kernelCharacter`:
the neighborhood of `x` is the preimage of that kernel under `y ↦ y*x⁻¹`.
Combining its local constancy with `eval_isLocallyConstant` composed with
`n ↦ n*s(l)` proves `kernelFunction_isLocallyConstant`. Quotient openness then
proves `integrandFunction_isLocallyConstant`. No topology on `V` or on `C` is
used.

For compact support, the published actual `splitStagesKernelSlice ... f l`
has values `f(n*s(l))` and compact closed quotient support.
`support_integrandFunction_subset` proves that a nonzero localized value can
occur only in that support, because a zero original value remains zero after
weighting and projection. It claims a subset, not equality: localization may
shrink support. `integrandFunction_hasCompactSupport` takes the closure inside
that compact closed set. The slice is built from actual induction in stages
and split-kernel restriction, not from a comparison premise.

Finally `integrand` is exactly `compactlySupportedSimpleFunc` applied to this
function and the two preceding proofs. `integrand_mk` retains the representative
formula by reduction. `integrand_finMeasSupp` uses finiteness on compact sets to
prove finite-measure support for every supplied quotient measure with that
property. No Haar measure or normalization is needed for these elementary
regularity facts. The comparison statement,
`SplitStagesCharacterComparisonStatement`, additionally retains all
the ordinary comparison's kernel-closedness, compact-open basis, regular left
and right Haar measure and compatible quotient measure assumptions; this
helper does not replace those assumptions.

The module allows zero coefficient modules and arbitrary smooth complex
representations. It imposes no admissibility, irreducibility, finite dimension,
finite length, nonzero-vector, discrete-group, compact-group, finite-index or
trivial-intersection-character condition. The unused declared universe `uW`
does not occur in these single-coefficient helper declarations; the later
pairwise statement uses both independent `uV,uW`.

## Direct proof inputs and transitive boundaries

The two direct project imports are
`Langlands.Representation.Induction.SplitStagesComparison` and
`Langlands.Representation.Induction.SplitKernelLocalizationData`. The new
proofs use their actual kernel equivalence, slice, subgroup action and
intersection inclusion; `Jacquet.Localization.mk_apply_subgroup`; and the
published `compactlySupportedSimpleFunc`/`_finMeasSupp`. Scalar cancellation,
quotient descent/openness, continuous subgroup inclusion, support closure,
and compact-subset reasoning use Mathlib. No new axiom or proof hole is used.

The slice's transitive mathematical route is `compactStagesEquiv` followed by
`splitKernelCompactEquiv`: actual evaluation, covariance, open stabilizers,
closed quotient support and a split-kernel quotient homeomorphism. The generic
Haar ratio is the existing quotient of automorphism Haar characters. Its
transitive route uses positive characters, Haar uniqueness and subgroup
conjugation. The localized action uses relation spans, quotient universal
properties and the actual section. These are the proof dependencies of the
helper, as opposed to every declaration incidentally loaded by its imports.

The broader import closure also contains published ordinary relative-integral,
compact averaging, normal-coinvariant kernel and induction-in-stages proofs.
They are elementary group/measure/linear algebra, and do not use their later
segment or derivative consumers.
`compactInductionNormalCoinvariantKernel` is a published proof, as recorded in
`notes/audits/external-library-2026-10-29/induction-whittaker-smooth.md`, P3-089.

Two incidental boundaries need explicit mention. First,
`Induction.StructuralStatement` is imported by `CompactQuotientProof`. It
contains Prop-valued definitions of smooth Frobenius, induction exactness and
open-subgroup adjunction, among other clauses. No proof of those adjunction or
exactness clauses is loaded or used by this helper or the slice. The closure
contains no reference to those clause names outside that defining module
except its import. Second, `Category.Basic` imports Mathlib finite-length
infrastructure and defines `HasFiniteLength`; this is not a representation
finite-length theorem. The elementary `Tensor.Finite`, block/parabolic,
inverse-transpose and local-field-normalization modules are incidental through
`CompactAutomorphismIntegralProof → CompactAutomorphism → InverseTranspose`.
Their tensor construction/smoothness, matrix and modulus facts are not segment
tensor, derivative or classification inputs. No later consumer theorem supplies
missing lower mathematics.

## Complete project import closure

The following is the complete recursively computed project-module closure of
the two imports at Library commit `7ad6e7323f2d14f5ccf8d30daa428878acda72c4`
(100 modules; the new helper itself is additional). Every edge
was compared with the actual source. Mathlib imports are
external foundations, pinned to Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The list includes statement
modules as declarations, not evidence that their propositions are true.

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

The checks in the following table cover the direct proof references just
listed and the complete transitive project closure. Every excluded family
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
| Plus functors, adjunction, BZ77 §4.13(d) submodule detection, general Leibniz, arbitrary-character Whittaker finiteness and the six mixed-minus clauses of `Derivative.MirabolicProductMinusCompatibilityStatement` | No such conclusion is invoked or proved. Adjunction proposition definitions are incidental as explained above; no adjunction theorem is an input. Ordinary compact induction, actual stages, quotient integration and Haar covariance are present, with the prescribed Haar ratio, and are independently upstream of these consumers. This helper supplies none of those six comparison clauses. |


Mixed normalization, LeftPhi and the final assembly, and
Phi/Mackey/right-Phi/exactness and downstream E1, lie outside this helper;
these boundaries are not hypotheses or proof evidence. Compiling this helper,
or its presence in the Library, does not establish the comparison;
`splitStagesCharacterComparison` in `SplitStagesCharacterComparison` proves it.
