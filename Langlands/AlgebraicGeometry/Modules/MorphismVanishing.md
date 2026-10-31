# Zero tests for module-sheaf morphisms and their pullbacks

This module contains four existing helpers extracted from
`ResidueLocalChartProof` for reuse by that proof and
`SectionVanishingTransportProof`. It imports the actual scheme-module
constructions in `SectionLocus` and Mathlib's additive-adjunction API.
All schemes remain in an arbitrary universe `u`.

- `Langlands.SchemeModule.structureModule_hom_eq_zero_iff` says that a
  morphism from the structure module is zero exactly when its value at one
  on global sections is zero. Naturality and linearity determine every
  component from that value.
- `Langlands.SchemeModule.map_eq_zero_iff_of_natIso` says that naturally
  isomorphic functors into a category with zero morphisms send any given
  morphism to zero simultaneously. It uses naturality and cancellation
  by the isomorphism components.
- `Langlands.SchemeModule.pullback_map_comp_eq_zero_iff` applies that
  criterion to the canonical comparison between successive and composite
  module pullback.
- `Langlands.SchemeModule.pullback_map_iso_eq_zero_iff` says that module
  pullback along a scheme isomorphism preserves and reflects zero. Its
  proof pulls back along the inverse and uses the composition and identity
  comparisons.

These are derived internal results, originally proved by Worker 354 as
private helpers named `unit_hom_eq_zero_iff`, `natIso_map_eq_zero_iff`,
`pullback_comp_eq_zero_iff` and `pullback_iso_eq_zero_iff` in
`ResidueLocalChartProof`. The Integrator moved and renamed those declarations
without changing their statements or proof arguments. Both consumers now
reuse these declarations; the duplicate helper proofs in the section
transport contribution have been removed.
