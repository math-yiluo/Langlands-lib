# Measures on a left homogeneous quotient

This internal construction equips the actual `Γ \ H` carrier from
`Langlands.Global.LeftCosetSpace` with the measure induced by a supplied set of
representatives. It uses the inherited quotient measurable space. It does not
postulate a measure satisfying the desired invariance laws.

For a group `H`, a subgroup `Γ`, a measurable space on `H`, a measure `ν` and
a set `s ⊆ H`, `quotientMeasure Γ ν s` is

\[
 (\operatorname{mk}_\Gamma)_*(\nu|_s).
\]

It is defined even when `s` is not a fundamental domain. The projection from
the restricted measure is measure preserving. For a measurable set `A` in the
quotient its measure is `ν (mk Γ ⁻¹' A ∩ s)`, and the total mass is `ν s`.
Scaling `ν` scales this quotient measure by the same nonnegative extended real
factor.

`normalizedMeasure Γ ν s` scales this measure by `(ν s)⁻¹`. It is proved to
be a probability measure only under the explicit conditions
`ν s ≠ 0` and `ν s ≠ ⊤`. Finiteness of the unnormalized measure similarly
requires `ν s ≠ ⊤`; no finite-volume conclusion is built into a definition.

`integral_quotientMeasure` is the pushforward integration identity for an
almost everywhere strongly measurable quotient function with values in any real
normed space `E`. `integrable_quotientMeasure_iff` separately identifies its
Bochner integrability with integrability of its pullback on `s`. The integral
identity alone does not establish convergence.

Independence of `s` requires `Γ` to be countable, its left multiplication to be
measurable, `ν` to be invariant under this action, and both proposed domains to
satisfy Mathlib's `IsFundamentalDomain Γ _ ν`. This predicate requires null
measurability, almost everywhere coverage and pairwise almost everywhere
disjoint translates. Pinned Mathlib proves equality of the two restricted
pushforwards. `quotientMeasure_eq` specializes that theorem to this left
homogeneous quotient; `quotientMeasure_compatible` gives the corresponding
`QuotientMeasureEqMeasurePreimage` structure. Equality of the normalized
measures follows from equality of the measures and their total masses.

When multiplication on `H` is measurable and `ν` is invariant on both sides,
`measurePreserving_rightTranslate` proves that positive right translations
preserve the quotient measure. Right translation takes a left fundamental
domain to another such domain because left and right multiplication commute.
Domain independence and right invariance upstairs then give the setwise
measure identity. `smulInvariant_quotientMeasure` packages this as invariance
under the opposite-group point action. The normalized measure is also
preserved by every right translation.

`automorphize Γ f` specializes Mathlib's orbit sum to this quotient, with
representative value

\[
 \sum_{\gamma\in\Gamma} f(\gamma x).
\]

This is a totalized infinite sum; its definition makes no summability claim.
The unfolding theorem assumes `Integrable f ν` and almost everywhere strong
measurability of the orbit sum for the constructed quotient measure. It
decomposes the ambient integral over the translates of the fundamental domain,
uses the finite norm integral to interchange sum and integral, and then uses
the pushforward identity. Thus it has the left-subgroup convention throughout
and requires no normality hypothesis.

For a Polish ambient space with its Borel sigma algebra and a second countable
`T0` quotient, `quotient_borelSpace` identifies the inherited quotient
measurable structure with the Borel structure of the quotient topology.
This is a separate topological qualification, not an input to the elementary
measure construction.

The provenance is internal: this module specializes pinned Mathlib's
`MeasureTheory/Group/FundamentalDomain.lean`, the measure and integral
pushforward APIs, `Topology/Algebra/InfiniteSum/Module.lean` and
`MeasureTheory/Constructions/Polish/Basic.lean`. Its unfolding proof adapts
the pinned right-coset proof in
`MeasureTheory/Measure/Haar/Quotient.lean` to the left subgroup action.
No original reduction-theory theorem is identified here.

The actual rational subgroup's countability, discreteness and fundamental
domain existence, an actual Haar measure, reductive unimodularity, positive
finite covolume, compact unipotent quotients, the split-centre comparison and
adelic specialization remain separate obligations. In particular the
uncountable split-centre-times-rational subgroup cannot be substituted for
`Γ` in these countable-domain results without a different construction.
