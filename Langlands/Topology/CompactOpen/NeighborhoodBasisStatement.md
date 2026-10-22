# Compact open subgroups in identity neighborhoods

`Langlands.CompactOpenSubgroupBasis` is a proposition definition, universally
quantified over a type `G` in an arbitrary universe, a `Group G`, a topology,
`NonarchimedeanGroup G`, and `WeaklyLocallyCompactSpace G`. It asserts that for
every set `U` belonging to the neighborhood filter of the identity, there is
`K : OpenSubgroup G` such that `IsCompact (K : Set G)` and `(K : Set G)` is
contained in `U`. A neighborhood need not itself be open.

This definition states a target; it does not install a typeclass, assert an
axiom, or supply a proof. It uses Mathlib's existing group and open-subgroup
types. In particular, no replacement locally profinite group structure is
introduced.

## Hypotheses and provenance

This is an internally derived bridge from Mathlib's interfaces. Mathlib's
`NonarchimedeanGroup` already extends `IsTopologicalGroup` and provides open
subgroups inside all identity neighborhoods; it does not assume that those
subgroups are compact. `WeaklyLocallyCompactSpace` says that each point has a
compact neighborhood. The target has no Hausdorff or other separation
assumption. Mathlib derives `WeaklyLocallyCompactSpace` from
`LocallyCompactSpace`, so a proof implies the assigned result with
`LocallyCompactSpace` and `T2Space`.

The motivating terminology is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter I: *Analysis on profinite groups*,
revision April 18, 2024, Section 6, printed/PDF page 8, opening definition of an
LP group. Casselman defines an LP group to have a Hausdorff topology and a
compact-open subgroup neighborhood basis. He does not state the present
nonarchimedean/local-compactness bridge there. Our target is an internal
consequence of Mathlib's hypotheses, not a claim that Casselman's definition
proves that bridge, and not a formalization of van Dantzig's theorem.

- Literature ID: `casselman-2024-profinite-analysis`.
- Source SHA-256:
  `16c37c57578aa1463c5625744cdade16416c5afb16b9e2203f13de4355a70270`.
- Actual retained original:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter I - Analysis on profinite groups--2024.pdf`.

## Interface audit and intended proof obligations

Worker 6 searched the pinned `Mathlib/Topology/Algebra/Nonarchimedean` sources
and inspected `Basic.lean`, `OpenSubgroup.lean`, `Topology/Defs/Filter.lean`,
and `Topology/Compactness/Compact.lean`. The following existing interfaces
suffice:

- `exists_compact_mem_nhds` supplies a compact neighborhood of the identity.
- `NonarchimedeanGroup.is_nonarchimedean` supplies an open subgroup inside
  its intersection with the requested neighborhood.
- `OpenSubgroup.isClosed` proves that subgroup closed; the required
  `SeparatelyContinuousMul` follows from the topological group instance.
- `IsCompact.of_isClosed_subset` makes that subgroup compact.

The intersection construction explains why no separation hypothesis is needed.
The Lean file here contains only the proposition definition; its proof will
be submitted separately against this exact accepted target.

## Exact dependencies and validation boundary

There are no project mathematical dependencies. The imports are
`Mathlib.Topology.Algebra.Nonarchimedean.Basic` and
`Mathlib.Topology.Compactness.LocallyCompact`.
The prepared environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`:
Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Compilation checks elaboration; it does not establish independent acceptance.
