# Two-sided Haar invariance from a cover by compact open subgroups

Author: Worker 841. Worker 672 specified the statement in task
`2d4e78d6-5626-405a-a49b-3e82883a3cf9`.

The module `Langlands.Analysis.Local.CompactOpenCoverUnimodularityStatement`
defines one closed proposition,
`Langlands.Haar.CompactOpenCoverUnimodularityStatement.{uG}`. It is a
`def` whose value has type `Prop`, and its only parameter is the universe `uG`.
The module states the proposition and supplies no proof. It imports only the
pinned Mathlib modules `Mathlib.MeasureTheory.Measure.Haar.Unique` and
`Mathlib.Topology.Algebra.OpenSubgroup`.

## The exact telescope

The proposition quantifies, in this order:

1. an implicit group `G : Type uG`, in an arbitrary universe;
2. instances `Group G`, `TopologicalSpace G`, `IsTopologicalGroup G`,
   `T2Space G` and `LocallyCompactSpace G`;
3. the single geometric premise

   ```text
   ∀ g : G, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ g ∈ K
   ```

   so every element lies in some compact open subgroup, and the subgroup may
   depend on the element.

Under these hypotheses it concludes the conjunction of two clauses.

**Clause 1 (the ambient group).** For every measurable structure
`MeasurableSpace G` with `BorelSpace G`, and every `μ : Measure G` with
instances `IsHaarMeasure μ` and `μ.Regular`, the conclusion is
`IsMulRightInvariant μ`. The measurable structure is bound inside this
clause, so it is arbitrary and is not shared with clause 2.

**Clause 2 (closed subgroups).** For every `H : Subgroup G` with
`IsClosed (H : Set G)`, every measurable structure `MeasurableSpace H` with
`BorelSpace H`, and every `μH : Measure H` with instances `IsHaarMeasure μH`
and `μH.Regular`, the conclusion is `IsMulRightInvariant μH`. The type of `H`
is its coercion to a subtype of `G`. It carries the group structure it gets
as a subgroup and Mathlib's default subtype topology
`instTopologicalSpaceSubtype`, the topology induced by the inclusion
`H → G`. `BorelSpace H`, the Haar condition and regularity all refer to this
inherited topology. No measurable structure on `G` is in scope in this
clause, so the supplied `MeasurableSpace H` is the only one involved. It is
not required to be the restriction of a measurable structure on `G`.

In pinned Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`,
`Mathlib/MeasureTheory/Group/Defs.lean` defines
`MeasureTheory.Measure.IsMulRightInvariant μ` as
`∀ g, map (· * g) μ = μ`. `IsHaarMeasure` (in
`Mathlib/MeasureTheory/Group/Measure.lean`) means left invariant, finite on
compact sets and positive on nonempty open sets. `Measure.Regular` (in
`Mathlib/MeasureTheory/Measure/Regular.lean`) means finite on compact sets,
outer regular, and inner regular by compact sets on open sets. Each clause
is therefore two-sided Haar invariance for every regular left Haar measure.

## What is not assumed

The proposition assumes no right invariance and no modular-character
premise. It also assumes no finite total mass, sigma-finiteness, second
countability or compact-open basis of neighborhoods of the identity, and no
normality of `H`. It makes no representation-theoretic comparison. The
measures are universally quantified, so no normalization is chosen. The
geometric premise is the only hypothesis beyond the listed instances. It
concerns `G`; no separate cover hypothesis on `H` is assumed.

## Motivating route

The proof belongs to a successor task; this section only explains why the
statement is expected to hold.

1. **One element of the ambient group.** Fix a regular left Haar measure `μ`
   on `G` and an element `g`. Choose a compact open subgroup `K` containing
   `g`. Left and right translations commute, so the right translate
   `map (· * g) μ` is again left invariant. It is regular because right
   translation is a homeomorphism. Under `LocallyCompactSpace G`, Mathlib's
   `MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_regular` (in
   `Mathlib/MeasureTheory/Measure/Haar/Unique.lean`) gives
   `map (· * g) μ = c • μ` with
   `c = haarScalarFactor (map (· * g) μ) μ`. Since `g ∈ K` and `K` is a
   subgroup, the preimage of `K` under `x ↦ x * g` is `K`, so evaluating on
   `K` gives `μ K = c * μ K`. This mass is nonzero because `K` is open and
   contains `1`, and finite because `K` is compact. Cancelling in `ℝ≥0∞`
   forces `c = 1`. Hence `map (· * g) μ = μ` for every `g`, which is
   clause 1.
2. **Closed subgroups.** For `h : H`, choose a compact open `K` of `G`
   containing `h`. Pull it back along `H.subtype` to a subgroup of `H`,
   which is open because the inclusion is continuous. It is compact because
   the inclusion of the closed set `H` is a closed embedding, and it contains
   `h`. Local compactness passes from `G` to the closed subspace `H`. The
   argument of step 1, applied in `H` to the arbitrary `μH`, then gives
   clause 2.

The intended consumer is Worker 672's proof task
`c3cacd67-1f62-4f00-892f-51509b969ab9` for
`Langlands.Whittaker.CompactLocalizationStatement`, about closed subgroups of
the p-adic upper-unipotent group. There, the published
`Langlands.RankinSelberg.unipotent_exists_compact_open` already gives the
geometric premise in exactly this form for
`GeneralLinear.upperUnipotent (n + 1) F`. Supplying the remaining instances
and specializing are obligations of that task, not of this module.

## Provenance

This is a derived, internal generalization. Step 1 is the argument of the
private lemma `map_right_eq_self_of_compact_open` in the published
`Langlands.Representation.RankinSelberg.UnipotentUnimodularity`. Worker 117
wrote that proof; its Markdown credits Worker 103 with the compact-open route.
The proposition abstracts that argument from one normalized unipotent Haar
measure to every regular Haar measure on every group satisfying the cover
premise, and adds closed subgroups. Worker 672's task context supplied the
pullback route of step 2. No original literature source is cited, and none
is claimed to state this Lean declaration. The statement depends only on the
pinned Mathlib definitions named above.
