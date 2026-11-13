# Locally constant fibre dimension gives a locally constant relative dimension

Author: Worker 50.

Helper module for the proof of
`Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement` (SGA 3, Exposé VI_B,
Corollaire 4.4). It turns the dimension hypothesis of that statement, local constancy of
`s ↦ topologicalKrullDim (f.fiber s)`, into a relative dimension for the residue fibres that
is constant on a neighbourhood of each base point.

## Declarations

- `Langlands.GroupScheme.ReducedBaseSmooth.topologicalKrullDim_eq_of_smoothOfRelativeDimension`:
  for a field `k`, a nonempty scheme `X` and `f : X ⟶ Spec k` with
  `SmoothOfRelativeDimension n f`, the topological Krull dimension of `X` is `n`.
- `Langlands.GroupScheme.ReducedBaseSmooth.exists_open_smoothOfRelativeDimension_fiber`:
  for `f : X ⟶ S` such that every residue fibre map `f.fiberToSpecResidueField s` is smooth,
  every fibre `f.fiber s` is a connected space, and `s ↦ topologicalKrullDim (f.fiber s)` is
  locally constant, each `s : S` has an open neighbourhood `U` and a natural number `n` with
  `SmoothOfRelativeDimension n (f.fiberToSpecResidueField t)` for all `t ∈ U`.

## Proofs

The first statement rewrites the topological Krull dimension as the supremum of the local
dimensions at points (`SchemeFiberGeometry.topologicalKrullDim_eq_iSup_at` from the Library).
Each local dimension equals `n` by the Library theorem `fieldSmooth_topologicalKrullDimAt`,
and the supremum of a constant family over a nonempty type is that constant.

For the second, at each `t : S` the Library theorem `smoothConnectedRelativeDimension`
(a smooth morphism with connected source has a constant relative dimension) applied to the
fibre gives `m` with `SmoothOfRelativeDimension m` for the fibre at `t`. A connected space is
nonempty, so the first statement gives `topologicalKrullDim (f.fiber t) = m`. Take `n` the
relative dimension at `s` and `U` the fibre of the locally constant dimension function through
its value at `s`; this set is open. For `t ∈ U` the two dimensions agree, so the cast of `m`
equals the cast of `n` in `WithBot ℕ∞`, hence `m = n`.

These are standard facts (a smooth scheme of relative dimension `n` over a field has
dimension `n`); the formulation is internal to this proof.
