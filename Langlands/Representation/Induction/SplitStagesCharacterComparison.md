# Natural character-localized compact induction in split stages

This file proves `Langlands.Induction.splitStagesCharacterComparison` with
exact type
`Langlands.Induction.SplitStagesCharacterComparisonStatement.{uG,uL,uV,uW}`.
The entry module is
`Langlands.Representation.Induction.SplitStagesCharacterComparison`. It imports
the published target and `Langlands.Representation.Induction.CharacterTwistProof`.
The theorem constructs both representation equivalences, proves their prescribed
integral evaluations, and proves the actual naturality equation for every
intertwiner between the two independently universe-valued coefficient modules.

## Derived provenance and original source

This is internal derived compact-induction/localization mathematics. It is not
attributed to Bernstein and Zelevinsky as a literal arbitrary-group theorem.
The original motivation is Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, retained at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
content SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The retained original was read at PDF pages 5, 11–12, 19, 27 and 32; the formulas
on PDF pages 5 and 27 were also checked in rendered page images. The
Library's `notes/errata` has no errata file for this source.

Sections 1.7–1.8, printed p.444 / PDF p.5, give the Haar change of variables,
right-translation induction and quotient by the relations
`rho(u)v - theta(u)v`. The source includes normalization factors in its
functors. The present source action is the published unnormalized section
action, and its target retains the explicitly specified Haar ratio; no
half-density or other normalization is inserted. Sections 3.1–3.2, printed
pp.450–451 / PDF pp.11–12, motivate the split-group applications. Proposition
4.13(b,c), printed p.458 / PDF p.19, and section 7.2, printed p.471 / PDF p.32,
motivate later functorial comparisons. Those assertions, their plus-functor
clauses, and their other consequences are not assumed here. Section 5.17,
printed p.466 / PDF p.27, explicitly uses the inverse character in the relative
integral and then reduces by an inverse twist. The implemented proof follows
that elementary twist idea, using already published actual quotient,
compact-induction and integral equivalences instead of assuming any source
comparison. This explains the provenance of the construction and its greater
group-theoretic generality.

## Exact binders and actual data

The final theorem has four independent universe parameters `uG,uL,uV,uW`.
It proves the existing proposition as a whole, without changing its definition.
Thus all its original binders and their order are retained. The group
`G : Type uG` has a topology making it a locally compact Hausdorff topological
group. The independent group `L : Type uL` is a topological group. The actual
homomorphisms `r : G →* L` and `s : L →* G` are continuous and satisfy
`r (s l) = l`. The subgroups `H ≤ P ≤ G` are closed and `r.ker ≤ P`.
Section containment is only
`hsH : ∀ l : P.comap s, s (l : L) ∈ H`, as in the target.

The character `theta : SmoothCharacter ℂ r.ker` has its actual open kernel.
The single supplied invariance hypothesis is
`SectionInvariant r s theta.toMonoidHom`. The proof reuses the published
`SplitStagesCharacter.kernelCharacter`, `sectionInvariant`, `section_mem` and
`subgroup_closed`: they derive the nested character, nested section invariance,
section containment and closedness from the actual ambient maps and hypotheses.
No theorem-valued nested comparison or extra invariance premise is supplied.
Use the following actual objects:

```text
K       = P.comap s
rP      = splitStagesRetraction r s hrs P hker
sP      = s.subgroupComap P
HP      = H.subgroupOf P
phi     = (Subgroup.subgroupOfEquivOfLe hHP).toMonoidHom
sigmaP  = sigma.comp phi
thetaP  = theta.toMonoidHom.comp
            (splitStagesKernelEquiv r s hrs P hker).toMonoidHom
A       = SplitKernelLocalization.kernelIntersection rP HP
eta     = SplitKernelLocalization.intersectionCharacter rP thetaP HP
I       = HP.comap rP.ker.subtype
C_sigma = Jacquet.Localization.Coinvariants sigmaP A eta
lambda_sigma = SplitKernelLocalization.subgroupAction
                 rP sP thetaP derivedInvariance HP hsHP sigmaP
chi     = Jacquet.complexCharacter
            (splitKernelHaarRatio rP sP HP hsHP hHPclosed)
kappa_sigma = twist chi lambda_sigma.
```

In particular the final target carrier is exactly compact induction of the
action on `C_sigma`, not compact induction of a replacement isomorphic module.
The existing `coefficientAction_mk` exposes its actual action:

```text
kappa_sigma l [v] = (chi l : ℂ) •
  [sigmaP (SplitKernelLocalization.subgroupSection sP HP hsHP l) v].
```

For `alpha(l)(n) = sP(l)⁻¹ * n * sP(l)`, `splitKernelHaarRatio` is precisely
`mulEquivHaarChar(alpha(l)|I) / mulEquivHaarChar(alpha(l))`. It is the
subgroup-to-kernel factor for forward precomposition by this inverse
conjugation, not its reciprocal. This same `chi` is used throughout the
comparison and the naturality map.

The proposition retains local compactness of `rP.ker`; measurable and Borel
structures on `rP.ker`, `I` and `LeftQuotient I`; the supplied quotient measure
`nu` finite on compact sets; and regular left Haar, right invariant measures
`muN` on `rP.ker` and `muI` on `I`. It retains
`IsCompatible I muN muI nu`, closedness of `r.ker`, and compact-open subgroup
neighborhood bases at one on both `G` and `rP.ker`. They are passed unchanged
to the ordinary comparison. No new normalization of any measure is imposed.

Finally `V : Type uV` and `W : Type uW` are arbitrary additive commutative
complex modules, carrying arbitrary smooth `H` representations `sigma,tau`.
Zero modules are included. No admissibility, irreducibility, dimension, length,
nonzero-vector, compact-group, discrete-group, finite-index,
character-triviality or universe-saturation condition is added. The construction
of an equivalence for one carrier does not mention the other carrier.

## The actual quotient transports

Write `xi = characterExtension r s hrs theta.toMonoidHom htheta`. Its
restriction to the kernel is `theta` and its value on every `s(l)` is one.
`inverseExtension` bundles `xi⁻¹` as an actual smooth character of `G`.
The open-kernel proof uses the already proved `smoothCharacterExtension` and
the equality of the kernels of a unit-valued character and its inverse.
Put `sigmaT = twist (xi⁻¹.comp H.subtype) sigma` and
`sigmaTP = sigmaT.comp phi`. `twisted_smooth` proves smoothness using the
published smooth-twist theorem and the continuous preimage of the open
extension kernel under `H.subtype`.

`ordinaryIntersectionEquiv` identifies
`Jacquet.Coinvariants sigmaTP A` with
`Representation.Coinvariants (sigmaTP.comp (rP.ker.subtype.subgroupComap HP))`.
The group map is exactly `SplitKernelLocalization.intersectionEquiv rP HP`:
it exchanges the two subgroup-membership proofs and leaves the ambient group
element unchanged. The forward map is the actual `Jacquet.lift`, justified by
the target coinvariant relation for that element; the inverse is the actual
`Representation.Coinvariants.lift`, justified by the reverse relation. Quotient
induction proves both inverse laws. `ordinaryIntersectionEquiv_mk` explicitly
sends the class of each `v` to the class of that same `v`.

`extension_intersection` proves that the restriction of `xi` to `A` is exactly
`eta`, using `characterExtension_kernel` and `splitStagesKernelEquiv`.
`extension_subgroupSection` proves its value on the actual nested section
is one. Applying the published `twistSectionEquiv` with these two facts,
then `ordinaryIntersectionEquiv`, gives `coefficientUntwist`. It is an actual
`K` representation equivalence from `lambda_sigma` to the ordinary section
action `splitKernelCoefficientAction rP sP HP hsHP sigmaTP`.
The imported twist comparison identifies the actual relation submodules by
multiplying the twisted relations by character units and their inverses.
The remaining intertwining proof in this file checks quotient representatives;
the extension factor disappears because it is one on the section. Both
`coefficientUntwist_mk` and `coefficientUntwist_symm_mk` expose the forward and
inverse identity-on-classes formulas. Thus no abstract carrier identification
hides an intersection character or a residual extension twist.

For the source, `inductionUntwist` composes `extensionTwistEquiv` with the
section restriction of `normalCoinvariantsEquiv` for
`compactInductionTwistEquiv H inverseExtension sigma`. This is an actual
`L` representation equivalence from the prescribed localized source to
`((compactInduced H sigmaT).toCoinvariants r.ker).comp s`. Its representative
formula `inductionUntwist_mk` sends `[f]` to `[F]`, where

```text
F(g) = (xi(g)⁻¹ : ℂˣ) • f(g).
```

The published compact-induction twist preserves the exact quotient support,
uses the intersection of the old right stabilizer and the open character
kernel, and supplies a genuine inverse. It therefore needs no new compactness
or dimension hypothesis.

## Comparison and canonical integral evaluation

`comparisonEquiv` is the composition of three actual representation
equivalences:

1. `inductionUntwist` on the source.
2. The published `splitStagesCompactEquiv` for the smooth representation
   `sigmaT`, with the original compatible measures and both given bases.
3. `compactInducedEquiv K` of the `chi` twist of
   `coefficientUntwist.symm`.

The third step transports the ordinary coefficient back to exactly `C_sigma`
with action `kappa_sigma`; its underlying linear map has no scalar factor.
The Haar character is inherited unchanged from step 2. Each inverse law and
equivariance law comes from the bundled equivalences, so bijectivity is
constructed, not assumed as a comparison premise.

`comparisonEquiv_eval_mk` proves the prescribed canonical integral formula.
Let `F` be the weighted function above and let `Q` be the published ordinary
`quotientCoinvariantSimple` of its actual `splitStagesKernelSlice` at `l`.
The ordinary comparison's evaluation is the supplied-measure integral of
`Q`. The proof shows an equality of actual simple functions

```text
Q.map coefficientUntwist.symm.toLinearMap
  = SplitStagesCharacter.integrand ... sigma hsigma f l.
```

Simple-function extensionality reduces this equality to a quotient
representative `n : rP.ker`. The inverse coefficient transport sends the
ordinary class to the same localized class. Multiplicativity of `xi`,
`xi(s(l)) = 1`, and its kernel restriction give
`xi (((n : P) : G) * s l) = thetaP n`. Consequently the value is precisely

```text
Jacquet.Localization.mk sigmaP A eta
  (((thetaP n)⁻¹ : ℂˣ) •
    eval H sigma f.val (((n : P) : G) * s l)).
```

This is the published `integrand_mk` formula, with the inverse sign intact.
The actual integrand already descends by cancellation of the intersection
character in the localized relation, is locally constant, and has support in
the compact closed kernel slice. It is the published
`compactlySupportedSimpleFunc` package, not a chosen integrable function.
Finally `AlgebraicIntegral.integral_linearMap`, using the ordinary simple
function's proved finite-measure support, moves the inverse coefficient
transport through the integral. This proves the exact evaluation at every
`f,l`, with no hidden scalar, inverse Haar ratio or measure rescaling.

## Naturality and the final proposition

For `T : sigma.IntertwiningMap tau`, let

```text
M = twistIntertwining chi
      (SplitKernelLocalization.subgroupMap rP sP thetaP derivedInvariance
        HP hsHP (restrictAlongMap phi T)).
```

The actual underlying linear map sends `[v]` to `[T v]`.
`integrand_natural` proves equality of the canonical simple functions for
`compactInducedMap H T f` and the source integrand postcomposed by
`M.toLinearMap`. Extensionality on a quotient representative gives
`[thetaP(n)⁻¹ • T(f(n*s(l)))]` on one side and
`[T(thetaP(n)⁻¹ • f(n*s(l)))]` on the other. They agree by complex linearity;
unit scalar multiplication is explicitly reduced to complex scalar
multiplication. This argument makes no identification between `V` and `W`.

`comparisonEquiv_natural` reduces an arbitrary actual localized source class
`z` to `[f]` using `Jacquet.Localization.mk_surjective`. The actual source map
`sectionMap ... (compactInducedMap H T)` sends `[f]` to `[T ∘ f]`.
Extensionality of compact functions reduces the desired equality to evaluation
at each `l : L`. Applying both `comparisonEquiv_eval_mk` formulas and
`integrand_natural` reduces it to
`AlgebraicIntegral.integral_linearMap`. The needed finite-measure support is
exactly the published `integrand_finMeasSupp`, valid because `nu` is finite on
compact sets. Thus the right side is exactly `compactInducedMap K M`, with
the prescribed Haar twist and coefficient quotient map.

The final theorem unfolds only the target's let bindings, chooses
`comparisonEquiv` for `sigma` and `tau` before any `T` is introduced, and
supplies both evaluation formulas and the naturality theorem. Its entire type
is the existing four-universe statement. No global saturated family or
same-carrier reduction is used.

## Actual proof dependencies and scope boundaries

The actual mathematical inputs are
published elementary character-extension and section-localization transports,
ordinary coinvariant lifts and quotient induction, scalar twist equivalences,
compact induction in stages, normal coinvariant comparison, split-kernel
compact functions, relative quotient integration and its Haar covariance,
and finite-fiber algebraic integral linearity. The canonical coefficient and
integrand helper is reused unchanged. The target is a Prop-valued definition
and supplies no comparison proof.

More explicitly, the ordinary `splitStagesCompactEquiv` composes
`compactStagesEquiv`, normal coinvariant transport and
`normalSplitCompactEquiv`, with the inner
`splitKernelCompactEquivariantEquiv`. Its lower relative-integral bijectivity
uses the published compact averaging, local sections, local inverse and kernel
proofs. The published normal-coinvariant kernel proof is an actual proof input,
not a statement or an unproved proposition; its Library status is also recorded in the
published audit `notes/audits/external-library-2026-10-29/induction-whittaker-smooth.md`,
finding P3-089. These are group, measure and linear-algebra results upstream of
all the excluded consumers. No general derivative theorem, Leibniz filtration,
representation finite-length theorem or consumer comparison is needed.

The proof's two direct project imports are the exact target module and
`CharacterTwistProof`. The latter is the only added imported module beyond the
target and its closure. Its implemented input is the elementary function
multiplication `compactInductionTwistEquiv`; it proves scalar-twist compatibility
from actual function covariance, an open stabilizer and exact support
preservation. It uses no adjunction, derivative or representation-theoretic
finiteness result.

The complete import closure does contain `Induction.StructuralStatement`:
it defines Prop-valued smooth Frobenius, induction exactness and open-subgroup
adjunction clauses. No proof of these clauses is loaded or used; their names
occur only in that defining module and import lines. `Category.Basic` loads
Mathlib's finite-length predicate and defines `HasFiniteLength`, without
loading a representation finite-length theorem. The incidental
`Tensor.Finite`, block/parabolic, inverse-transpose and local-field
normalization modules enter through
`CompactAutomorphismIntegralProof → CompactAutomorphism → InverseTranspose`.
They provide elementary tensor construction/smoothness, matrices and modulus
facts, not segment tensor, derivative, irreducibility or classification
conclusions. The sole occurrence of the word Whittaker in these project Lean
sources is an elementary matrix-homeomorphism convention comment in
`Group.GL.Maps`; it is not a finiteness theorem. All imported project source
was checked for the forbidden consumer families, and the direct mathematical
proof route was checked separately. Incidental proposition definitions are
not treated as proofs of their contents.

## Complete project import closure

This is the complete recursively computed project closure of both direct
imports at Library commit `a8934c89b9ba4ec0a4ce1a27cee0290064384404`: 103
imported modules, excluding only the present proof entry module. Mathlib
foundations are pinned to Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

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
Langlands.Representation.Induction.SplitKernelIntegral
Langlands.Representation.Induction.SplitKernelLocalizationData
Langlands.Representation.Induction.SplitKernelSectionAction
Langlands.Representation.Induction.SplitQuotientProof
Langlands.Representation.Induction.SplitQuotientStatement
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

## Condition-by-condition independence audit

The following checks apply to the actual proof references above and to the
complete transitive project closure just listed. They include every named
consumer's mathematical conclusions, the modules that prove them and downstream
consequences. This table retains the conditions of the published
statement audit; the proof's actual extra import, `CharacterTwistProof`, was
checked separately as described above. A proposition definition, citation
or conditional assembly is not a proved
input.

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
| Plus functors, adjunction, BZ77 §4.13(d) submodule detection, general Leibniz, arbitrary-character Whittaker finiteness and the six mixed-minus clauses of `Derivative.MirabolicProductMinusCompatibilityStatement` | No such conclusion is invoked or proved. Adjunction proposition definitions are incidental as explained above; no adjunction theorem is an input. Ordinary compact induction, actual stages, quotient integration and Haar covariance are present, with the prescribed Haar ratio, and are independently upstream of these consumers. The generic comparison proved here supplies none of those six separate comparison clauses. |


## Validation and scope boundaries

The exact theorem was checked with a successful
Lake build and declaration inspection exposing levels `[uG,uL,uV,uW]`.
The only reported axioms are `propext`, `Classical.choice` and `Quot.sound`.

This module constructs only the generic comparison. Mixed normalization,
LeftPhi and the final assembly, and Phi/Mackey/right-Phi/exactness and
downstream E1, are separate; `Derivative.MirabolicProductMinusLeftPhiStagesComparison`
and `Derivative.MirabolicProductMinusRightPhiIdentityGroups` import this module.
No mixed-minus clause of `MirabolicProductMinusCompatibilityStatement`,
plus functor, adjunction theorem, BZ77 4.13(d) submodule detection, general
Leibniz theorem or Whittaker finiteness conclusion is proved or assumed here.
The matrix `plusSubgroup` construction is not needed.
