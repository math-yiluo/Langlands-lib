# The closure of a local occurrence in a Hilbert space

Module `Langlands.TraceFormula.IsotypicTrace.OccurrenceClosure`. Part of the reduction of
`GroupSchemeCuspidalIsotypicTraceFactorizationStatement` to one local occurrence.
It is internal to that reduction; its results are standard facts about admissible
representations, proved here from Library material.

## Setting

`Gv` is a topological group with Borel structure. Sections that need it also assume `Gv`
Hausdorff, locally compact, totally disconnected and second countable. `σ : Gv →* (E →L[ℂ] E)`
acts on a complex Hilbert space `E`, `ρ : Representation ℂ Gv V` acts on a complex vector space,
and `j : V →ₗ[ℂ] E` satisfies `j (ρ y x) = σ y (j x)` (an *occurrence* of `ρ` in `E`).

## Results

* `testFunction_orbit_integrable`: for a measure finite on compacts, a Schwartz–Bruhat function
  `f` and continuous orbits, `y ↦ f y • σ y x` is Bochner integrable. The integrand is
  continuous with compact support.
* `map_integratedAction`: for smooth `ρ` and continuous orbits,
  `j (Hecke.integratedAction μ ρ hρ f x) = ∫ y, f y • σ y (j x) ∂μ`. Proof: pair both sides with
  an arbitrary `z ∈ E`. The left side is computed by `Hecke.integratedAction_dual` for the
  linear functional `⟪z, j ·⟫`, and the right side by `integral_inner`.
* `toRepresentation σ` is the algebraic representation underlying `σ`.
  `injective_of_isIrreducible`: if `ρ` is irreducible and `j ≠ 0`, then `j` is injective. This is
  `Representation.IsIrreducible.injective_or_eq_zero` for the intertwiner defined by `j`.
* `exists_isCompact_openSubgroup_le`: every open subgroup contains a compact open subgroup. This
  is the Library's `Topology.LocallyProfiniteProof.vanDantzig`.
* `mem_range_of_mem_closure_of_fixed`: let `μ` be a Haar measure, `σ` norm preserving with
  continuous orbits, and `ρ` admissible. Then every vector `w` of the closure of the range of `j`
  that is fixed by an open subgroup `K` lies in the range of `j`. Proof: choose a compact open
  `L ≤ K` and let `Φ` integrate the indicator of `L` against `σ`
  (`Langlands.Analysis.integratedIsometricAction`). By `map_integratedAction` and
  `Hecke.integratedAction_mem_fixedVectors`, `Φ` maps the range of `j` into the image `F` of the
  `L`-fixed vectors of `ρ`. `F` is finite-dimensional by admissibility, hence closed, so `Φ` maps
  the closure into `F`. Since `w` is `L`-fixed, `Φ w = μ(L) • w`, so `w ∈ F`.
* `exists_fixed_preimage_of_mem_closure`: if moreover `j` is injective, such a `w` is `j v` for a
  `K`-fixed `v`.
* `exists_linearMap_lift`: a linear map with values in the range of an injective linear map
  factors through it.
