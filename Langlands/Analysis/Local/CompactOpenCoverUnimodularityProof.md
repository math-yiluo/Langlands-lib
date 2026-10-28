# Two-sided Haar invariance for compact-open covered groups

Worker 117 proves the published closed proposition
`Langlands.Haar.CompactOpenCoverUnimodularityStatement.{uG}` by the closed
theorem `Langlands.Haar.compactOpenCoverUnimodularity` in
`Langlands.Analysis.Local.CompactOpenCoverUnimodularityProof`.
The universe `uG` is arbitrary. The theorem has no additional parameters or
hypotheses. Its only import is the unchanged statement module.

The proposition concerns every locally compact Hausdorff topological group
`G` for which each element belongs to some compact open subgroup. Its first
clause gives right invariance for every supplied regular left Haar measure
on `G`, with any compatible Borel structure. Its second clause gives the
same conclusion for every closed subgroup `H`, with the inherited topology
and any compatible Borel structure on `H`. The two measurable structures
are quantified independently in the two clauses. No normalization is chosen.

## Implemented ambient proof

The private helper `map_right_eq_self_of_compact_open` treats an element
`g` of one compact open subgroup `K` and a regular left Haar measure `μ`.
Right translation is the homeomorphism `Homeomorph.mulRight g`, so
`Regular.map` gives regularity of `map (fun x => x * g) μ`. Mathlib's
existing instance makes this measure left invariant, since left and right
translations commute.

The pinned theorem
`MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_regular` then gives

```text
map (fun x => x * g) μ = c • μ,
c = haarScalarFactor (map (fun x => x * g) μ) μ.
```

Because `g ∈ K`, subgroup multiplication and cancellation show that the
preimage of `K` under this translation is `K`. Evaluating the equality on
the open, hence measurable, set `K` gives `μ K = c * μ K` in `ℝ≥0∞`.
The mass `μ K` is nonzero because `K` is open and contains `1`, and finite
because `K` is compact. `ENNReal.mul_eq_right` cancels this mass, forcing
`c = 1`; the measure equality becomes right invariance under `g`.

The private helper `rightInvariant_of_compactOpenCover` chooses a compact
open subgroup separately for each element and applies this argument. The
first conclusion clause applies it to the arbitrary supplied ambient
measure and Borel structure.

## Closed subgroups

For a closed subgroup `H`, `hH.locallyCompactSpace` supplies local
compactness of its inherited topology. Its group, topological group and
Hausdorff structures are the existing subtype instances.

Given `h : H`, choose a compact open subgroup `K` of `G` containing its
image. Define

```text
L = OpenSubgroup.comap H.subtype continuous_subtype_val K.
```

Its carrier is the preimage of `K` under the subtype inclusion, it is open
by continuity of that inclusion, and it contains `h`. Closedness of `H`
makes the inclusion a closed embedding, so
`hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK` proves that `L` is
compact. This derives the entire compact-open cover premise for `H` from
the ambient premise. Applying `rightInvariant_of_compactOpenCover` inside
`H` proves the second clause for the arbitrary supplied measure and Borel
structure on `H`.

The proof uses no normality, finite total mass, countability, compact-open
neighborhood basis, right-invariance premise, modular character, or
representation-theoretic input.

## Provenance and dependencies

This is an internal generalization, not a transcription of a literature
theorem. Worker 117 adapted the private ambient scalar-cancellation lemma
of the same name in the published
`Langlands.Representation.RankinSelberg.UnipotentUnimodularity`.
Worker 117 authored that Lean proof, and Worker 103 supplied its
compact-open-subgroup route. Worker 672 supplied the closed-subgroup
pullback route in this task's context. Worker 841 authored the target
statement from Worker 672's specification. The current module imports only
that published statement; it does not import the representation module.

The measure, homeomorphism, subgroup and compactness results are from
Mathlib at pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`. The proof preserves the target
Lean/Markdown pair and all its imports. Specialization to p-adic groups,
quotient measures and character localization belongs to the consumer task
and is outside this module.
