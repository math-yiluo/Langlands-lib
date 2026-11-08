# Conditional unitary detection by the actual split-center point image

Authors: Worker 200 and Worker 1567.

## Provenance and scope

`Langlands.Plancherel.conditionalRationalSplitCenterUnitaryDetection` proves
the published proposition
`Langlands.Plancherel.ConditionalRationalSplitCenterUnitaryDetectionStatement.{u}`
at every field universe `u`. This is an internal, derived adapter between
published interfaces. Worker 200 supplied the shared Lean proof draft;
Worker 1567 checked its interfaces and prepared this paired contribution.

The field is an arbitrary nonarchimedean local field, in equal or mixed
characteristic. The connected reductive group scheme `M` need not be split
or quasisplit. For a supplied morphism `s : T.toGrp ⟶ M`, the theorem retains
`IsSplitComponent s`, injectivity of `GroupScheme.characterRestrict s`,
and all three local-point premises:

- `CentralNormKernelCompactness M hM`;
- `CentralDerivedNormKernelCocompactness M hM`;
- `DerivedSmoothRealAnnihilation M hM`.

The conclusion is `IsUnitaryDetecting` for exactly
`(GroupScheme.rationalPoints.map s).range`. Thus every complex character
of `M(F)` with open kernel and norm one on this actual point image has
norm one everywhere. The topology is the canonical
`rationalPointTopology F M.X`, using the affine structure furnished by
connected reductivity.

## Implemented proof

The Lean proof introduces every quantified datum and hypothesis in the
published proposition. It installs the affine instances and the canonical
rational-point topology required by that proposition.

Write `A = (GroupScheme.rationalPoints.map s).range`,
`Λ = rationalDiscreteValuationImage M`, and
`p = rationalValuationImageProjection M`. The published theorem
`finite_rationalValuationQuotient_of_injective hM s hs hinj` provides
the local instance `Finite (Λ ⧸ A.map p)`.

The proof then applies
`Langlands.HarishChandraSchwartz.isUnitaryDetecting_of_norm_eq_one_on_ker`
to this same subgroup `A` and projection `p`. Its remaining hypothesis
requires every complex character with open kernel to have norm one on
`p.ker`. Rewriting membership by `rationalValuationImageProjection_ker`
identifies that subgroup with `rationalCommonNormKernel M`. The published
`norm_eq_one_on_rationalCommonNormKernel_of_structure` proves the required
norm-one assertion from the three supplied local-point premises.

The invoked generic theorem uses finiteness of `Λ ⧸ A.map p` to put a
positive power of any group element in `A` times `p.ker`, then deduces
norm one for the original element. Its hypotheses require no continuity
of the projection `p`.

## Retained obligations

The proof does not discharge rational-character restriction injectivity
or any of the three local-point premises. In particular, it preserves
the scheme-derived rational-point subgroup used by those premises
without identifying it with the abstract commutator subgroup. It proves
the stated conditional detection assertion and makes no claim about
representations, temperedness, integrability, spectral finiteness, or
the Plancherel theorem.
