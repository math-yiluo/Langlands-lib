# Integration over closed semidirect products compatible with a lattice

Module `Langlands.Global.EisensteinConstantTerm.UnfoldingAnalytic`, namespace
`Langlands.Global.LeftCosetSpace`.

## Conventions

`𝒢` is a locally compact, second countable, Hausdorff group with its Borel structure, and
`R ≤ 𝒢` is discrete. For a subgroup `X`, `latticeOf R X` is `R ∩ X` as a subgroup of `X`
(`isDiscrete_latticeOf`). Closed subgroups are locally compact
(`locallyCompactSpace_of_isClosed_subgroup`) and subgroups are second countable
(`secondCountableTopology_subgroup`); both are used as local instances.

## Results

Let `H`, `K`, `A` be closed subgroups of `𝒢` with `K, A ≤ H`, `K` normal in `H`, `K ∩ A = 1`,
`H = K A`, and such that the `A`-component of every element of `H ∩ R` lies in `R`.

- `exists_retraction_of_semidirect`: a continuous retraction `H → A` with kernel `K`
  (from `exists_continuous_retraction`).
- `semidirect_haar`: for such a retraction and compact covers of `K ∩ R` in `K` and `H ∩ R` in
  `H`, the retraction carries `H ∩ R` into `A ∩ R`, a compact set meets every orbit of `A ∩ R`,
  conjugation by `A` preserves Haar measure on `K`, and the normalized Haar measure of `H` is the
  image of the product of the normalized Haar measures of `K` and `A`.
- `setIntegral_latticeOf_eq_of_semidirect`: given compact sets meeting every orbit of `K ∩ R` in
  `K` and of `H ∩ R` in `H`, a compact set meets every orbit of `A ∩ R` in `A`, and for every `f`
  with values in a real normed space, left invariant under `K` and under `H ∩ R`,
  `∫_{fd(H ∩ R)} f = ∫_{fd(A ∩ R)} f`, all measures normalized by the intersections with `R`
  (`normalizedHaar`) and all fundamental domains the chosen ones.

## Provenance

This is the integration formula `∫_{(H ∩ R) \ H} f = ∫_{(A ∩ R) \ A} f` for `K`-invariant `f` and
`H = K ⋊ A`, used for the unipotent radicals in the proof of Bernstein–Lapid Lemma 6.10. It is
derived from `UnfoldingSemidirect` and `UnfoldingLattices`.
