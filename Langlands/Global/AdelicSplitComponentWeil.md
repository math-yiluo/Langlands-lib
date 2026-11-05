# Intrinsic orbital averaging and change of actual split component

Author: Worker 112.

This internal construction combines the intrinsic normalized full subgroup Haar
from `AdelicSplitCenterHaarIndependence`, its exact transport from
`AdelicSplitComponentHaar`, the quotient comparison from
`AdelicSplitComponentIndependence`, and the full subgroup Weil construction
in `AdelicSplitCenterWeil`. It exposes orbital averaging and Weil compatibility
without supplied splitting coordinates, and proves that averaging and its
integrability are preserved when the supplied actual split component changes.

## Objects, hypotheses and fixed measures

Let `F : Type u` be an arbitrary number field, `G` a group scheme over
`Spec F` whose underlying scheme is affine and locally of finite type over
`F`, `T` a commutative group scheme, and `i : T.toGrp ⟶ G`. The actual
rational-character restriction `characterRestrict i` is assumed injective
with finite-index range. For the construction on one torus, the additional
inputs are scheme-theoretic centrality `hc : IsCentral i` and the split-torus
property `hT : IsSplitTorus T.toGrp`.

Write `H = AdelicGroupPoints F G`, `S = positiveRationalSubgroup F G T i`,
and `Q = PositiveRationalQuotient F G T i`. The subgroup `S` is generated
by the actual positive torus image and the principal rational points. The
quotient is the existing left homogeneous quotient with the right relation;
its ambient right action sends `[g]` to `[g * x]`. No normality of the
principal subgroup is assumed.

The subgroup measure `μS` is
`intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hc hT`. It is the
already constructed intrinsic form of normalized positive Haar times counting
on `rationalNormOneSubgroup F G`, pushed forward by actual multiplication.
Its normalization uses the fixed ambient Haar `μH = Measure.haar` on `H`
and the fixed norm-one Haar on `normOneSubgroup F G`. The quotient measure
`ν` remains `positiveRationalQuotientHaarMeasure F G T i`, obtained from
the fixed norm-one principal quotient measure by actual inclusion.
This module changes none of these measures.

The split-torus property supplies finite splitting coordinates internally.
No coordinates are parameters of the intrinsic average or the intrinsic
compatibility and component-comparison results. The universe is unrestricted,
and the finite splitting index may be empty, so rank zero is included.

## Intrinsic averaging and compact-test fibers

`intrinsicPositiveRationalSubgroupHaarMeasure_isMulRightInvariant` proves
right invariance of `μS` by extracting a finite splitting from `hT` and
applying the existing full subgroup right-invariance theorem.

`intrinsicPositiveRationalQuotientAverage` is `quotientAverage S μS`.
Its representative formula, proved by reflexivity in
`intrinsicPositiveRationalQuotientAverage_mk`, is

`A(f)([g]) = ∫ h : S, f (h.val * g) ∂μS`.

Right invariance of `μS` makes this a well-defined function on `Q`.
The definition accepts every function `f : H → ℂ`; the integral is Lean's
total Bochner integral, so the definition alone asserts no convergence.

For every finite splitting `e : T.toGrp ≅ splitTorus (Spec F) I`,
`intrinsicPositiveRationalQuotientAverage_eq` identifies this function
exactly with `positiveRationalQuotientAverage` constructed using `I` and
`e`. The proof descends to quotient representatives and rewrites the
subgroup measure using
`intrinsicPositiveRationalSubgroupHaarMeasure_eq`. It requires no
regularity or integrability assumption on `f`.

For continuous compactly supported `f`,
`integrable_intrinsicPositiveRationalSubgroup_fiber` separately proves
integrability of `h ↦ f (h.val * g)` for every `g : H`. The proof
chooses finite splitting coordinates, rewrites to the existing subgroup
measure, and applies `integrable_positiveRationalSubgroup_fiber`.
Neither this fiber result nor the definition and coordinate comparison
assume right invariance of norm-one Haar.

## Intrinsic Weil compatibility

This section additionally assumes
`IsMulRightInvariant (Measure.haar : Measure (normOneSubgroup F G))`.
`intrinsicPositiveRationalQuotientHaarMeasure_isCompatible` establishes
`IsCompatible S μH μS ν`. Thus the exact quotient measure is nonzero and
regular, every ambient right translation preserves it, and continuous
compactly supported complex tests satisfy both the integrability and
integral-formula fields of the existing compatibility definition.

The implemented proof chooses finite splitting coordinates, uses
`positiveRationalQuotientHaarMeasure_isCompatible`, and rewrites its subgroup
measure to `μS`. It introduces no new product decomposition or scalar.
The two consequences are exported separately:

- `integrable_intrinsicPositiveRationalQuotientAverage` proves that `A(f)`
  is integrable with respect to `ν`.
- `integral_intrinsicPositiveRationalQuotientAverage` proves
  `∫ q, A(f)(q) ∂ν = ∫ g, f g ∂μH`.

Both results require continuity and compact support of `f` and the stated
norm-one right-invariance premise. Together with the independent fiber
integrability theorem, they provide convergence of both stages of the
displayed Weil integral.

## Changing the supplied actual split component

Let `T'`, `i'` have their own injective finite-index character restriction.
Assume `hs : IsSplitComponent i` and `hs' : IsSplitComponent i'`.
These supply the centrality and split-torus properties needed for the two
intrinsic subgroup measures, denoted `μS` and `μS'`. All ambient and
norm-one measure choices remain fixed.

The existing continuous group equivalence
`E = splitComponentSubgroupEquiv F G T i T' i' hs hs'` preserves ambient
representatives and transports `μS` exactly to `μS'`.
The existing measurable quotient equivalence
`C = splitComponentQuotientMeasurableEquiv F G hs hs'` sends `[g]` to
`[g]` and transports `ν` exactly to `ν'`. The following results use
these two published measure-preserving maps.

`integrable_intrinsicPositiveRationalSubgroup_fiber_iff` proves, for every
function `f : H → ℂ` and every `g : H`, that its subgroup fiber is
integrable with respect to `μS` if and only if the corresponding fiber
is integrable with respect to `μS'`. The proof uses
`MeasurePreserving.integrable_comp_emb` for the measurable embedding
underlying `E`. Its pullback fiber is the same ambient function because
`E` preserves ambient representatives.

`intrinsicPositiveRationalQuotientAverage_splitComponent` proves
`A'(f)(C(q)) = A(f)(q)` for every `q : Q` and arbitrary `f`.
The proof uses quotient induction, the representative formula for `C`,
and `MeasurePreserving.integral_comp` for `E`. This equality concerns
total integrals; convergence is supplied separately when needed.

`integrable_intrinsicPositiveRationalQuotientAverage_iff` proves
`Integrable A(f) ν ↔ Integrable A'(f) ν'` for arbitrary `f`.
It applies `MeasurePreserving.integrable_comp_emb` for `C` and rewrites
the pullback average with the preceding pointwise identity.

Finally, `integral_intrinsicPositiveRationalQuotientAverage_splitComponent`
proves equality of the two total quotient integrals. It uses
`MeasurePreserving.integral_comp'` for `C` followed by the pointwise
identity. None of these four component-change results assumes continuity,
compact support, measurability or integrability of `f`, or right invariance
of norm-one Haar. The two integrability equivalences transfer convergence
when it holds; neither they nor the total-integral equalities assert that
arbitrary functions are integrable.

## Provenance and retained obligations

All content is derived internally from the named actual subgroup and quotient
constructions, exact normalized Haar transports, and Mathlib's
measure-preserving change-of-variables results. No external structural
assertion or source theorem is added.

The character injectivity and finite-index assumptions remain explicit for
each torus map, as do the affine and locally finite-type hypotheses on `G`.
The construction is conditional on supplied central split tori or actual
split components. Existence of suitable data for every connected reductive
group, the general-number-field identification with the greatest Q-split
centre after restriction of scalars required by the Getz–Hahn convention,
analytic unimodularity, finite volume and reduction theory remain separate
obligations. In particular, the norm-one right-invariance premise in the
Weil section is retained.
