# Intermediate intersection coordinates and composite normalization

This is an internal continuation of the supplied literal subgroup coordinates
in `OrderedSubgroupFactorization`. Waldspurger (2003), IV.1, printed p.279
(PDF p.45), uses an ordered product of complementary unipotent groups and
the resulting iterated integral. IV.1(12), printed p.283 (PDF p.49), states
composition when parabolic distances add. The construction here supplies a
coordinate and measure step for already given charts; existence of those
charts for actual reductive radicals remains separate.

Let `D : OrderedSubgroupFactorization U₀ U₁ U₂ V W` in any topological
group carrier. The group operations need not be continuous for this unit.
The existing record supplies homeomorphisms

- `(U₀ ∩ U₁) × V ≃ₜ U₁`;
- `(U₁ ∩ U₂) × W ≃ₜ U₂`;
- `(U₀ ∩ U₂) × (V × W) ≃ₜ U₂`,

with literal multiplication formulas, `V ≤ U₁`, `V ≤ U₂` and `W ≤ U₂`.
The notation for each intersection refers to the actual `subgroupOf`
subgroup in the indicated codomain.

`intersection_le_middle` proves `U₀ ⊓ U₂ ≤ U₁` from these three maps.
Given an endpoint-intersection element `g`, apply the inverse second chart
to write `g = j*w` and the inverse first chart to write `j = h*v`.
Since `j` and `v` lie in `U₂`, subgroup cancellation places `h` in `U₂`.
The two composite coordinate tuples `(h,(v,w))` and `(g,(1,1))`
therefore have the same image. Injectivity of the supplied composite chart
identifies their first coordinates, placing `g` in `U₁`. This does not
derive a root-distance assertion without the three supplied charts.

`intersectionFirst` constructs the required intermediate homeomorphism
`(U₀ ∩ U₂) × V ≃ₜ (U₁ ∩ U₂)`.
Because the second factor lies in `U₂`, the original first chart's value
lies in `U₂` exactly when its first coordinate does. Restrict that
homeomorphism to these subtypes, use the proved inclusion to identify its
domain with `(U₀ ∩ U₂) × V`, and interchange the two subgroup-membership
proofs in its target. These changes preserve the inherited topologies.
`intersectionFirst_eq` gives literal multiplication in `U₂`, and
`intersectionFirst_symm_snd` identifies the inverse second coordinate with
that of the original first chart. No normality or commutation is required.

For measures, supply measurable structures on `U₂`, its two intersection
subgroups, `V` and `W`. Let `μI₂₀`, `μV` and `μW` be S-finite.
`measurePreserving_composite_of_intersection` assumes exactly

- the constructed intersection chart sends `μI₂₀.prod μV` to `μI₂₁`;
- the second chart sends `μI₂₁.prod μW` to `μU₂`.

It proves that the existing composite chart sends
`μI₂₀.prod (μV.prod μW)` to `μU₂`. Literal multiplication and group
associativity identify it with the iterated chart; the measure-preserving
product associator and composition prove its normalization. No Borel-space,
Haar, regularity or local compactness hypotheses enter this implication.

The restricted first measure identity remains an application obligation.
It is not inferred by restricting Haar measure from the original ambient
group to a potentially null subgroup. Actual compact-open normalization
and comparison with the source's prescribed measures remain separate.
This unit establishes neither existence of the original three charts nor
analytic convergence, continuation or intertwiner composition, and closes
no whole-program Plancherel condition.
