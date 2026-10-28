# Vanishing of homogeneous anti-invariant distributions

`Langlands.HarmonicAnalysis.Distribution.homogeneousAntiInvariantVanishing`
proves the published
`HomogeneousAntiInvariantVanishingStatement.{uG, uX}`. The universes of the
group and the space remain independent.

Let a sigma-compact, locally compact nonarchimedean group `G` act transitively
and jointly continuously on a Hausdorff locally compact space `X`. Let `D` be
an algebraic distribution on `X`, invariant under every action homeomorphism.
For every homeomorphism `σ : X ≃ₜ X`, the equality `pushforward σ D = -D`
implies `D = 0`. The distribution is the full complex algebraic dual of the
Library's Schwartz–Bruhat functions. The homeomorphism has no required
compatibility with the action, and the space may be empty.

## Indicator values determine the distribution

The private lemma `eq_zero_of_characteristic_eq_zero` works on any topological
space. Suppose `D` vanishes on the characteristic test function of every
compact clopen set. A Schwartz–Bruhat function `f` has finite range by
`finite_range_of_locallyConstant_of_hasCompactSupport`. Its nonzero fibers
are clopen by local constancy and compact by `Hecke.TestFunction.isCompact_fiber`.

Index the nonzero values of `f` by the finite subtype
`S = {c : ℂ | c ∈ Set.range f ∧ c ≠ 0}`. For `c ∈ S`, let `φ c` be the
characteristic function of the fiber `f⁻¹({c})`. The proof checks pointwise
that `f = ∑ c : S, c • φ c`: at a point where `f` is zero every summand
vanishes; otherwise the unique surviving summand corresponds to that value.
Linearity and the assumed vanishing on the fiber indicators give `D f = 0`.
Extensionality then proves `D = 0`.

## Anti-invariance and positive comparison

The private lemma `eq_zero_of_positive_indicator_proportionality` assumes
positive rational proportionality between the values of `D` on all pairs
of nonempty compact clopen indicators. For a nonempty compact clopen set `U`,
put `V = σ⁻¹(U)`. The homeomorphism makes `V` compact, clopen and nonempty.
The comparison hypothesis supplies `q : ℚ` with `q > 0` and

`D(1_V) = (q : ℂ) * D(1_U)`.

The proof identifies `pullback σ (1_U)` with `1_V` pointwise. Evaluating the
anti-invariance hypothesis on `1_U`, using the Library convention
`(pushforward σ D)(f) = D(pullback σ f)`, gives

`D(1_V) = -D(1_U)`.

Consequently `((q : ℂ) + 1) * D(1_U) = 0`. Positivity gives `q + 1 ≠ 0`
in the rationals, and the cast to the complex numbers preserves this
inequality. Thus `D(1_U) = 0`. An empty set has zero characteristic function,
so every compact clopen indicator has zero value. The first lemma finishes
the argument. This also covers an empty `X` without choosing a base point.

## Assembly and provenance

The private lemma `homogeneousAntiInvariantVanishing_of_proportionality`
introduces precisely the telescope of the published vanishing proposition.
It uses group invariance to obtain the positive comparison premise and then
applies the preceding algebraic lemma. The public theorem supplies this
premise with the published theorem `homogeneousIndicatorProportionality`
from `Langlands.HarmonicAnalysis.Distribution.HomogeneousPositivityProof`.
That theorem proves the comparison by compact-open orbit partitions and
positive rational counting. Its implementation is imported unchanged.

This proof is an internal algebraic deduction from the published indicator
comparison, the finite-range and compact-fiber APIs, and the actual
Schwartz–Bruhat and distribution definitions. It uses no measure construction
or topology on the dual. The published statement's companion documents its
motivation in Bernstein–Zelevinsky (1976), Example 6.12, printed p.56; the
present file proves the Library's internal proposition by the reduction above.
Worker 128 implemented the reduction and assembly, following the final
positivity argument in Worker 33's task proof plan.
