# Natural quotient integration on compact induction

This module constructs the complex linear maps

\[
 I_\nu:\operatorname{cInd}_H^G(\sigma)\longrightarrow V_H,
 \qquad
 \overline I_\nu:(\operatorname{cInd}_H^G(\sigma))_G\longrightarrow V_H,
 \qquad
 I_\nu(f)=\int_{H\backslash G}[f(g)]\,d\nu(Hg).
\]

The integral is the actual finite-fiber algebraic integral from
`Langlands.HarmonicAnalysis.AlgebraicIntegral`, and both coinvariant spaces
are Mathlib's `Representation.Coinvariants`. The module proves the
representative formula, translation invariance, and naturality for every
algebraic intertwiner. It makes no bijectivity assertion.

## Parameters and conventions

`G : Type uG` is a group with a topology and `IsTopologicalGroup G`.
`H : Subgroup G` is any subgroup. The module applies in particular to a
Hausdorff group and a closed subgroup as requested by its construction task.
Neither separation nor closedness is needed here: the published compact
induction already supplies compact projected support, and its covariance
and local constancy make that support closed even without these assumptions.
There is no local compactness or nonarchimedean hypothesis on `G`.

`V : Type uV` has only `AddCommGroup V` and `Module ℂ V`, and
`σ : Representation ℂ H V` is arbitrary. No topology, norm, measurable
structure, completeness, dimension restriction, admissibility, finite length,
or smoothness of `σ` is assumed. The actual `CompactFunctions H σ` consists
of covariant functions with one open right stabilizer per function and compact
projected nonzero support. Its covariance is
`f(h * g) = σ h (f g)` and its action is right translation
`(compactInduced H σ g) f (x) = f(x * g)`.

The coset space is `QuotientIntegration.LeftQuotient H`, namely
`Quotient (QuotientGroup.rightRel H)`, whose points are the cosets `H * g`.
It is definitionally the quotient used by compact induction. For integration
it carries a supplied measurable structure satisfying `BorelSpace`, and
`ν : Measure (QuotientIntegration.LeftQuotient H)` satisfies
`IsFiniteMeasureOnCompacts ν`. Only translation invariance and the ambient
coinvariant descent require the additional hypothesis

```lean
hν : ∀ g : G,
  MeasureTheory.MeasurePreserving
    (Langlands.QuotientIntegration.rightTranslate H g) ν ν
```

Neither nonzero measure nor normalization is assumed. In particular zero
measure is allowed. Measure existence, nonzero normalization, bijectivity,
and normalizer equivariance are separate obligations.

## Construction and elementary laws

`coinvariant_eval_left_mul` proves that applying
`Representation.Coinvariants.mk σ` to evaluation removes the covariance:
the class of `σ h v` equals the class of `v`.
`quotientCoinvariantFunction H σ f` then uses the published
`QuotientIntegration.descend`, not a choice of coset representatives. Its
`_mk` theorem states its value at `quotientMap H x` is exactly
`Representation.Coinvariants.mk σ (eval H σ f.val x)`.

`quotientCoinvariantFunction_isLocallyConstant` uses the public
`eval_isLocallyConstant` theorem and the quotient topology: the inverse image
of every subset of the target is open because its pullback to `G` is open.
The target needs no topology. `support_quotientCoinvariantFunction_subset`
shows that projection of values can only shrink the original quotient
support. The `_hasCompactSupport` theorem puts the closure of this support
inside the original closed compact support, using
`isClosed_quotientSupport`. This proves compact topological support without
an additional support hypothesis.

`quotientCoinvariantSimple` applies the published
`compactlySupportedSimpleFunc` to this locally constant, compactly supported
function. Thus it is an actual `MeasureTheory.SimpleFunc` with exactly those
values, measurable fibers, and finite range. `quotientCoinvariantSimpleLinear`
bundles the proved addition and scalar laws. The `_finMeasSupp` theorem uses
finiteness of `ν` on compact sets to prove finite measure of the nonzero
support.

`compactCoinvariantIntegral H σ ν` is the complex linear map given by
`AlgebraicIntegral.integral ν (quotientCoinvariantSimple H σ f)`.
Its `_apply` theorem records that formula. Explicitly, for the resulting
simple function `F`, the value is

\[
 \sum_{v\in F.\mathrm{range}}
   \operatorname{ofReal}\bigl((\nu(F^{-1}\{v\})).\mathrm{toReal}\bigr)\,v.
\]

Each nonzero fiber has finite measure; the zero fiber contributes zero even
if its measure is infinite. Additivity and complex homogeneity are obtained
from the proved finite-support algebraic integral laws.

`quotientCoinvariantFunction_translate` identifies right translation with
precomposition by the actual quotient homeomorphism `rightTranslate H g`.
`compactCoinvariantIntegral_translate H σ ν hν g f` then follows from
`AlgebraicIntegral.integral_comp_measurePreserving`. Consequently
`compactCoinvariantDesc H σ ν hν` is defined by the actual
`Representation.Coinvariants.lift` of the integral. Its `_mk` theorem
identifies its value on the class of `f` with `compactCoinvariantIntegral`,
and `_mk_integral` states the finite-fiber formula directly.

For another module `W : Type uW`, representation `τ`, and arbitrary
`T : σ.IntertwiningMap τ`, `quotientCoinvariantFunction_natural` proves the
pointwise compatibility with `compactInducedMap H T` and the actual
`Representation.Coinvariants.map σ τ T`. Applying
`AlgebraicIntegral.integral_linearMap` gives
`compactCoinvariantIntegral_natural`. Quotient extensionality then proves
`compactCoinvariantDesc_natural`, the equality of linear maps

```lean
(compactCoinvariantDesc H τ ν hν).comp
    (Representation.Coinvariants.map (compactInduced H σ) (compactInduced H τ)
      (compactInducedMap H T)) =
  (Representation.Coinvariants.map σ τ T).comp
    (compactCoinvariantDesc H σ ν hν)
```

The companion `_natural_apply` is the pointwise version on an arbitrary
ambient coinvariant. The universes `uG`, `uV`, and `uW` remain independent.
The source carrier of `compactCoinvariantDesc` is in `Type (max uG uV)`,
and its target is in `Type uV`. Naturality is an equality of linear maps;
no category-level packaging forces these universes to coincide.

## Original source and scope of the formalization

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Ann. Sci. ENS (4) **10** (1977), 441–472, §5.17,
printed pp. 466–467 (PDF pages 27–28). Registered source:
`bernstein-zelevinsky-1977-induced-i`, file
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

On p. 466 the source defines `A` by integrating the projected induced
function over the subgroup quotient, with a character factor in the twisted
case. In its reduction to `N = {e}` and trivial character, rename the
source's ambient group `V` to `G`, its subgroup `V'` to `H`, and its inducing
space `L` to our coefficient module `V`. Its projection `p` is then the
projection to `H`-coinvariants, and its map is precisely
`f ↦ ∫_[H\G] [f(g)] dν`. Invariance under ambient translation gives its
map on ambient coinvariants; the source describes the construction as a
morphism of functors.

The current module isolates that untwisted map and proves its elementary
construction, descent, and naturality laws. The supplied-measure formulation
and the weakening to arbitrary topological groups are internal extensions
justified by the implemented proofs, not assertions that the source works
in that generality. The source's further assertion that `A` is an
isomorphism is proved on p. 467 using regular representations, free
resolutions, and exactness. None of those claims is made or presumed here.
All laws in this module are proved from the imported constructions; there
are no averaging, well-definedness, compactness, invariance, or naturality
assumptions replacing the laws. The only invariance input is the explicitly
supplied invariance of the measure itself.
