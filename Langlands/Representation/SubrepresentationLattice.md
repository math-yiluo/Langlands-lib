# The complete lattice of subrepresentations

Worker 249 supplies a complete lattice structure on Mathlib's
`Subrepresentation ρ`, for a representation `ρ : Representation A G W` of a
monoid `G` over a semiring `A`. The pinned Mathlib (commit `5ed29652`) gives
`Subrepresentation ρ` only a `Lattice` and a `BoundedOrder`. Neither Mathlib nor
the Library has arbitrary suprema or infima, which the compact-coefficient
isotypic and annihilator constructions need (`CompactCoefficient/Isotypic`).
This module is an internal infrastructure addition, not a literature result.

## Suprema and infima

All declarations are in the namespace `Langlands.Subrepresentation`.

- `instSupSet`: the supremum of a set `S` of subrepresentations has underlying
  submodule `⨆ s ∈ S, s.toSubmodule`. It is invariant because this submodule is
  below its own preimage under each `ρ g`. Every member of `S` lies below that
  preimage, because each `s` is invariant.
- `instInfSet`: the infimum has underlying submodule `⨅ s ∈ S, s.toSubmodule`.
  It is invariant because membership in a submodule infimum is membership in
  every member, and each member is invariant.
- `toSubmodule_sSup` and `toSubmodule_sInf` state these underlying submodules.
  Both hold by `rfl`.
- `instCompleteLattice` pulls back the complete lattice of `Submodule A W`
  along the injective map `toSubmodule`, using Mathlib's
  `Function.Injective.completeLattice`. The order is Mathlib's existing order
  of subrepresentations. The binary operations, top and bottom are Mathlib's
  existing `Max`, `Min` and `BoundedOrder` instances, and all compatibility
  equations hold by `rfl`. The structure therefore extends Mathlib's lattice
  and bounded order without an instance diamond. A development check confirmed
  that the projections of `instCompleteLattice` to `Lattice` and `BoundedOrder`
  equal Mathlib's `Subrepresentation.instLattice` and
  `Subrepresentation.instBoundedOrder` at reducible-and-instances
  transparency. That check is not part of this module.

## Indexed forms and transport

- `toSubmodule_iSup` and `toSubmodule_iInf` state that the underlying
  submodule of an indexed supremum or infimum, over any `Sort` index, is the
  corresponding indexed supremum or infimum of underlying submodules. They are
  proved by unfolding `iSup` and `iInf` as `sSup` and `sInf` of a range and
  using `iSup_range` and `iInf_range`.
- `mem_iInf`: a vector lies in `⨅ i, f i` exactly when it lies in every
  `f i`. The proof combines `toSubmodule_iInf` with `Submodule.mem_iInf`.
- `mapsTo_iSup`: let `φ : ρ.IntertwiningMap σ` be an actual intertwiner to a
  representation `σ` on another carrier `W'`, which may lie in a different
  universe. If `φ` maps every member `S i` of a family into a subrepresentation
  `T` of `σ`, then it maps `⨆ i, S i` into `T`. The proof shows the underlying
  submodule of the supremum is below the preimage `T.toSubmodule.comap
  φ.toLinearMap`. That preimage is a submodule containing each `S i`. It does
  not claim that a vector of the supremum lies in a single member.

No other result is proved. Arbitrary suprema of large families involve no
resizing: an indexed supremum is the supremum of its range in the fixed lattice
of subrepresentations of `ρ`.
