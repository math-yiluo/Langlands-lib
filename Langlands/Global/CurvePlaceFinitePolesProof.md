# Finite poles on actual function-field curve places

`Langlands.Global.curvePlaceFinitePoles` proves exactly the published
`Langlands.Global.CurvePlaceFinitePolesStatement` in one arbitrary common
universe `u`. The constants `k` are any perfect field, and `F` carries
compatible algebra structures over `k` and `RatFunc k` with
`FunctionField k F`. Every `x : F`, including zero, is integral at all but
finitely many of the actual `AlgebraicCurve.Place k F`. The proof does not
assume that the specified extension of `RatFunc k` is separable. Finite
constant fields and inseparable supplied rational-function presentations
are included.

The implemented proof first chooses a separating parameter. The given
function field is essentially of finite type over `k`. Mathlib's theorem
for perfect fields gives a finite separating transcendence basis, whose
cardinality is one by comparison with the basis provided by the original
rational parameter. If `s` is its unique element, Mathlib's function-field
finite-dimensionality theorem and the separating-basis conclusion show
that `F/k(s)` is finite and separable.

For any parameter with this finite separable property, the integral
closure of `k[s]` in `F` is a Dedekind domain. A proper valuation subring
containing `k` and `s` contains this integral closure. Its centre is a
nonzero prime, and the corresponding height-one localization is contained
in the original valuation subring: write an element of the localization
with denominator outside the centre, whose valuation is one. Equality
then follows from the published comparison theorem for a discrete
valuation subring contained in a proper valuation subring. Thus every
actual curve place containing `s` is the place of a height-one prime of
this chart. The chart places at which `x` is not integral are contained in
the image of Mathlib's finite height-one valuation support of `x`, and
are therefore finite.

The simple intermediate fields `k(s)` and `k(s⁻¹)` agree, by closure under
inversion. Transporting finite-dimensionality and separability along this
equality gives the second chart's finite pole set. Every valuation
subring contains `s` or `s⁻¹`, so the union of the two chart pole sets
contains every pole of `x`. The final finite-subset argument proves the
published proposition without an additional hypothesis.

The characteristic-independent chart comparison adapts the short proof
of `CurveModel.valuationSubringAtPrime_le` and its equality and
classification consequences in the published
`Langlands.AnthropicFLT.Definitions.Def_JacJ1_ChartAlgebra`. That module is
ported from the Anthropic Lean formalization of Fermat's Last Theorem,
commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, Copyright 2026
Anthropic, PBC, under Apache-2.0; see the Library files
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`. This proof
reuses its actual integral-closure charts and centre construction, and
replaces its characteristic-zero Dedekind-instance route with explicit
finite separability. All helper lemmas in the submitted module are
private. Worker 208 wrote this adaptation, the separating-parameter
argument and the two-chart assembly.

The inherited source is Brian Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), printed p.1, registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This is a derived arithmetic prerequisite for the diagonal action of a
global field on its adelic ring and the finite exceptional sets defining
its open levels. Conrad uses that background; the perfect-constant-field
generalization proved here is not attributed to a separate theorem in
his paper.

The result supplies finite poles for the existing concrete places. The
full-field adelic diagonal, comparison with other conventions for global
places, local compactness of completions and scheme or algebraic-space
point comparisons remain separate obligations. The finite set of poles
may be empty; Conrad's nonempty all-place level convention is a separate
condition.
