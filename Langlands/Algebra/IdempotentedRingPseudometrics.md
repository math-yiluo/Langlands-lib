# The source zero–one pseudometrics

This module constructs the family of zero–one pseudodistances ("écarts")
in David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, I.1.3, printed page 8 / PDF page 14,
and compares the uniformity and topology they define with the published
right-annihilator uniformity `idempotentedRingUniformSpace` of
`Langlands.Algebra.IdempotentedRingUniformity`.

The construction and its proofs are by Worker 6. Worker 1125 rechecked
them against the original source and the published prerequisite. Worker 1125
also added the `(a-b)e = 0` zero-locus form, the `Monotone` packaging, the
topology-of-infimum form and the extra interface checks, and prepared the
submission.

All declarations are in `Langlands.Algebra`. The pseudodistance API is in
`Idempotent`, and the common-upper-bound and directedness laws are in
`IsIdempotented`. The given `A : Type uA` has only `NonUnitalRing A`.
The construction uses its actual multiplication, the published
`Idempotent A` and corner order of `Langlands.Algebra.IdempotentedRing`,
and the published `Idempotent.rightAnnihilator`,
`Idempotent.rightCoordinateEntourage` and `idempotentedRingUniformSpace`.
It adds no unit, nontriviality, commutativity, countability or finiteness
premise. Zero rings, the zero idempotent and the resulting trivial
pseudometrics are all included. Every pseudometric, uniform and topological
structure here is an ordinary definition or term; none is a global instance.

## The pseudodistances

For `e : Idempotent A`, `Idempotent.rightPseudoDistance e a b : ℝ` is
`if a * e = b * e then 0 else 1`. The condition is decided classically
inside the definition, so no decidability hypothesis is added. Each
idempotent gives a separate function; the module defines a family of
pseudodistances, not one metric on `A`.

- `rightPseudoDistance_eq_zero_iff` describes the zero locus as `a * e = b * e`.
- `rightPseudoDistance_eq_zero_iff_sub_mul` gives the same zero locus as
  `(a - b) * e = 0`, using right distributivity and `sub_eq_zero`.
- `rightPseudoDistance_eq_zero_iff_annihilator` gives it as
  `a - b ∈ e.rightAnnihilator`, the published additive subgroup with
  carrier `{a | a * e = 0}`, which is the source's `A(1-e)`.
- `rightPseudoDistance_zero_or_one` says every value is `0` or `1`.
- `rightPseudoDistance_lt_one_iff` says distance `< 1` exactly when the
  right coordinates are equal.

Self-distance zero (`rightPseudoDistance_self`) and symmetry
(`rightPseudoDistance_comm`) follow from reflexivity and symmetry of
equality of coordinates. The triangle inequality
(`rightPseudoDistance_triangle`) is a case split on the three coordinate
equalities. If both adjacent distances are zero, equality is transitive.
Otherwise their sum is at least one, which bounds the endpoint distance.

`Idempotent.rightPseudoMetricSpace e : PseudoMetricSpace A` packages exactly
this function and these three proofs. All other fields (extended distance,
uniformity, topology, bornology) take Mathlib's defaults derived from the
distance. `rightPseudoMetricSpace_dist` records by reflexivity that its
distance is `rightPseudoDistance e`. The definition is marked
`@[instance_reducible]`, like the published uniform space, so it can be
installed locally.

## Order monotonicity and directedness

`rightPseudoDistance_mono` proves that `e ≤ f` in the published corner order
implies `d_e(a,b) ≤ d_f(a,b)`. The published antitonicity
`rightCoordinateEntourage_antitone` shows that `a * f = b * f` implies
`a * e = b * e`. So if the `f`-distance is zero, both distances are zero.
If it is one, the `e`-distance is at most one.
`rightPseudoDistance_monotone` restates this as
`Monotone (Idempotent.rightPseudoDistance (A := A))` for the pointwise order
on functions `A → A → ℝ`. These results need no idempotentedness.

For `hA : IsIdempotented A`,
`IsIdempotented.rightPseudoDistance_common_upper_bound` applies the published
`finite_upper_bound` theorem to the set `{e, f}`. It returns an actual
`g : Idempotent A` with the order witnesses `e ≤ g` and `f ≤ g`, together
with pointwise domination of both pseudodistances by `d_g`.
`IsIdempotented.rightPseudoDistance_directed` deduces that the family
`e ↦ d_e` is `Directed (· ≤ ·)`. Only these two results assume `IsIdempotented A`.

## Uniformity and topology comparison

`Idempotent.rightPseudoMetricSpace_uniformity` proves that the uniformity of
one pseudometric `rightPseudoMetricSpace e` is exactly the principal filter
`𝓟 e.rightCoordinateEntourage`. The proof compares filter membership using
Mathlib's standard basis `Metric.uniformity_basis_dist` of distance-ball
entourages. If `s` contains a ball `{p | d_e p < ε}` with `ε > 0`, then
`s` contains the coordinate entourage, because equal coordinates give
distance zero. Conversely, the radius-one ball is exactly the coordinate
entourage, by `rightPseudoDistance_lt_one_iff`.

`idempotentedRing_iInf_pseudometric_uniformSpace` proves
`(⨅ e, (rightPseudoMetricSpace e).toUniformSpace) = idempotentedRingUniformSpace A`.
It uses uniform-space extensionality, Mathlib's `iInf_uniformity`, the
published formula `idempotentedRing_uniformity` (the uniformity is
`⨅ e, 𝓟 e.rightCoordinateEntourage`) and the single-pseudometric formula above.
`idempotentedRing_iInf_pseudometric_topology` rewrites with this equality,
so the topology of the infimum uniform space is the published annihilator
topology. `idempotentedRing_iInf_pseudometric_topologies` states the same thing
with the infimum of the individual pseudometric topologies, via Mathlib's
`UniformSpace.toTopologicalSpace_iInf`. In Mathlib's order the infimum is the
coarsest structure finer than every member. This is the uniformity and topology
that the family of écarts defines. These comparisons hold for every
nonunital ring and need no idempotentedness. With `IsIdempotented A`, the
published prerequisite's `idempotentedRing_nhds_hasBasis` gives the
neighbourhood bases `{a | (a-b)e = 0}` of this common topology.

The closing `example`s check complete unapplied types at the arbitrary ring
universe `uA`. They cover the definition and its classical `if` formula, the
pseudometric package and its distance, the annihilator zero locus, the
zero–one range, monotonicity, the common upper bound and directedness. They
also cover the single-pseudometric uniformity, the uniform-space equality and
both topology comparisons.

## Source correspondence

The governing original is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
I.1.1–I.1.2, printed pages 6–7 / PDF pages 12–13, give the nonunital
conventions, the corner order and the definition of a ring with idempotents.
In I.1.3, printed page 8 / PDF page 14, Renard writes
`A(1-e) = {a - ae} = {a | ae = 0}`. He then introduces the écarts
`d_e : A × A → {0,1}` with `d_e(a,b) = 0` if `a - b ∈ A(1-e)` and `1` otherwise.
He states that they satisfy the axioms of écarts, that the family is
*filtrante* in the sense that `e ≤ f` implies `d_e ≤ d_f`, and that the
topology they define is the annihilator topology just defined.

- The Lean definition tests `a * e = b * e`. It agrees with the source formula
  by `rightPseudoDistance_eq_zero_iff_annihilator`. The values `0` and `1`
  are taken as real numbers so that the functions become Mathlib
  pseudometrics.
- The écart axioms are `rightPseudoDistance_self`, `rightPseudoDistance_comm`
  and `rightPseudoDistance_triangle`, packaged in `rightPseudoMetricSpace`.
- The filtrant property `e ≤ f ⇒ d_e ≤ d_f` is `rightPseudoDistance_mono` and
  `rightPseudoDistance_monotone`. The common upper bound and `Directed`
  statements under `IsIdempotented A` add the existence of upper bounds in the
  idempotent order, which Renard proves in I.1.2's lemma.
- The topology comparison is `idempotentedRing_iInf_pseudometric_topology`
  and `idempotentedRing_iInf_pseudometric_topologies`. The single-coordinate
  principal-filter formula and the uniform-space equality are internal,
  explicit forms of Renard's comparison. Renard does not present them in
  this form.

No project errata entry for this source exists. The registered errata for
the 2010 edition, `renard-2010-corrections-complements` (SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`), PDF
page 1, entry for printed p.9 line 15, corrects the inequality `d_f ≤ d_e`
to `d_e ≤ d_f`. The governing 2026 edition, printed p.8/PDF14, already has
the corrected direction, which `rightPseudoDistance_mono` proves.

## Scope

This unit proves no uniform additive-group laws, no separation, no
annihilator direct-sum or quotient comparison, and no inverse-limit topology.
It also proves nothing about density, completeness, completion
multiplication or the extension of module actions. Those remain separate
obligations.
