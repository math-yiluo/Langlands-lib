# Proof: rational points of the polynomial-locus analytification

The theorem `affineAnalytificationRationalPoints` proves the unchanged published
`AffineAnalytificationRationalPointsStatement.{u, v}`. The field and the
coordinate algebra have independent universes. The hypotheses are exactly those
of the statement: the field is nontrivially normed, ultrametric and complete,
and the commutative algebra has a supplied finite polynomial presentation.
All three clauses apply to zero variables, the zero algebra and nonreduced
algebras without additional assumptions.

This is an internal derivation from the Library's polynomial-locus atlas and
its actual saturation. The source meaning and formulation choices are those
documented in `AffineAnalytificationRationalPointsStatement.md`: Conrad–Temkin
2009, Example 2.3.2, printed pp.11–12; Conrad 2011, printed p.19, the final
paragraph of the proof of Proposition 5.11(3); and Berkovich 1990, Theorem 3.4.1
and Remark 3.4.2, printed pp.63–64/PDF pp.77–78. The proof implements the
Library's affine Berkovich-space statement directly.

The auxiliary module `FieldPointSaturation` was contributed by Worker 294. Its
character uniqueness argument develops Worker 669's original draft. The local
`SeminormTopology` namespace adapts the topological part of Worker 279's shared
Task 7083 draft, revision 1, with its own namespace and explicit omission of
unused completeness hypotheses. These are implemented proofs in this
contribution; no unpublished theorem is assumed as an input.

## Bijection for the constructed atlas

The existing map `toAlgPoint` recovers an algebraic point by evaluating on a
chart containing the given field point. For every chart containing that point,
`radiusAdmits_toAlgPoint` proves that the recovered coordinates satisfy its
radius bound: their values are those of the chart character, whose absolute
values are the given spectrum point, and the latter is bounded by the norm.
The norm bound for the coordinate completes this step.

`boundedEval` bundles the given character as a bounded homomorphism. The
coordinate values identify it with the constructed evaluation character by
`hom_ext_coordinate`. Consequently their spectrum points agree, and
`chart_spectrumPoint` identifies the ambient analytic point with the original
point. A base-field-valued point is determined by its underlying point: two
characters with the same absolute values agree on `b` by applying that equality
to `b` minus the scalar value of one character. This is proved in the saturation
helper module. It supplies the right inverse `toFieldPoint_toAlgPoint`. Together
with the published left inverse `toAlgPoint_toFieldPoint`, it gives
`toFieldPoint_bijective`.

## Evaluation topology

First, `pointSeminorm_analyticPoint_apply` computes the seminorm of an algebraic
point as `a ↦ ‖φ a‖`.

The local seminorm topology argument establishes that the map from the glued
analytic space to `A → ℝ` given by seminorm evaluation is a topological
embedding. The coordinate-algebra image is dense in each chart algebra, by
polynomial approximation followed by the surjective presentation map. Spectrum
seminorms are continuous functions on that algebra: the triangle inequality
and the norm bound give a Lipschitz bound. Thus agreement on the
coordinate-algebra image determines a chart spectrum point. Moving two charts
into a common larger chart gives global injectivity.

For the topology, a point in the `m`-th closed chart lies in the open disc bounded
by the next radius. On the next closed chart, the continuous injective seminorm
map is a closed embedding, using compactness of the spectrum and the Hausdorff
function-space target. Given a neighborhood in the analytic space, this chart
embedding supplies a neighborhood in the function space. Intersect it with the
finitely many strict coordinate inequalities defining that open disc. Every
point satisfying these inequalities is in the next chart, so this intersection
pulls back inside the prescribed neighborhood. This proves the inducing
property for the seminorm map.

Continuity of `analyticPoint` now follows from continuity of every
`φ ↦ ‖φ a‖`. For the reverse topology comparison, temporarily equip the
algebraic point set with the topology induced by `analyticPoint`. For each `a`
and each fixed `φ`, the function

`ψ ↦ ‖ψ a - φ a‖`

is the pullback of seminorm evaluation at `a - algebraMap K A (φ a)`, so it is
continuous. Its value at `φ` is zero. The norm criterion for convergence proves
continuity of `ψ ↦ ψ a` at `φ`. All evaluations are therefore continuous for the
induced topology, which proves that it equals the original evaluation topology.
The established point uniqueness gives injectivity and hence
`isEmbedding_analyticPoint`.

## Saturated atlas

`FieldPointSaturationComparison.saturationEquiv` preserves base-field-valued
points of any affinoid atlas and keeps their underlying points literally fixed.
Its separate Markdown describes how the full restriction universal property is
tested on the zero-variable affinoid algebra to extend characters to saturated
charts. The proof has independent field, space and chart-index universes.

`saturatedFieldPointEquiv` composes the bijection for the constructed atlas with
this saturation equivalence. Its point-preservation identity is reflexive in
Lean. The final theorem packages that equivalence and identity with the first
two clauses, at the exact published target.
