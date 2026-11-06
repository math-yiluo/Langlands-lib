# A dense adjoint slice through the centralizer of a torus Lie algebra

Author: Worker 1630.

This derived helper module proves the following. Let `G` be a smooth affine
group over a field `k` and `T₀ ⟶ G` a homomorphism from a torus. Take the
centralizer `𝔷` of `Lie(T₀)` in `Lie(G)`. Then the adjoint slice map
`G × 𝔷 ⟶ Lie(G)`, `(g, Z) ↦ Ad(g) Z`, has dense range. The project's route
to unirationality of the scheme of maximal tori (SGA 3, Exposé XIV) uses this
dominance statement. Worker 1420 requested the existential form
`exists_torusCentralizerSlice` for that route. The proof combines
`TorusRegularElement`, which gives a regular element over a splitting field,
with `AdjointSliceExtension`, which gives tangent-space dominance from a point
over a field extension. No external theorem is asserted.

All declarations live in the namespace `Langlands.GroupScheme.Lie`, except
`Langlands.GroupScheme.IsTorus.exists_infinite_isSplitTorus`. Finite Lie
coordinates `c : FiniteCoordinates G d` identify the Library's Lie algebra
`lieKernel G A` with `Fin d → A`. `adjointDifferentialFamily c Y` is the
coordinate matrix of `ad(Y)`, and `sliceMap (adjointRepresentation c) B` is
the morphism `G × 𝔸^r ⟶ 𝔸^d`, `(g, t) ↦ Ad(g) (B t)`, from
`AdjointDominance`. `IsTorus` is the Library predicate: the group becomes a
split torus after base change to some field extension. `algebraBaseMap k E`
is `Spec E ⟶ Spec k`.

- `IsTorus.exists_infinite_isSplitTorus`: a torus over `k` splits over an
  infinite field extension of `k`. Proof: take an algebraic closure of a
  splitting field. Splitting persists along the tower by the Library's
  `IsSplitTorus.baseChange_fieldTower`, and algebraically closed fields are
  infinite.

## Linear algebra

- `exists_mulVec_map_eq_of_commonKernel`: let `E` be a field extension of
  `k`, `M y` a family of square matrices over `k` and `B` a matrix over `k`.
  Assume every vector over `k` annihilated by all `M y` lies in the column
  space of `B`. Then every vector over `E` annihilated by all `M y` (entries
  mapped to `E`) lies in the `E`-column space of `B`. Proof: expand the
  vector in a `k`-basis of `E`. Each coordinate vector is annihilated over
  `k`, hence is `B` times some vector, and these recombine.

## The centralizer in coordinates

Here `G` is a group scheme over `Spec k` with affine structure morphism, `T₀`
a commutative group scheme over `Spec k` and `j₀ : T₀ ⟶ G`.

- `torusCentralizerCoordinates c j₀` (definition): the common kernel in
  `k^d` of `ad(j₀ Y)` over all Lie elements `Y` of `T₀`.
  `mem_torusCentralizerCoordinates_iff` unfolds membership.
- `torusCentralizerMatrix c j₀` (definition): the `d × r` matrix whose
  columns are Mathlib's chosen basis `Module.finBasis` of
  `torusCentralizerCoordinates c j₀`, with `r` its dimension.
- `adjointDifferentialFamily_torusCentralizerMatrix`: every `ad(j₀ Y)`
  annihilates every column.
- `exists_torusCentralizerMatrix_mulVec`: every vector annihilated by all
  `ad(j₀ Y)` is `torusCentralizerMatrix c j₀` times some vector.
- `targetMap_mem_elementCentralizerLie_torusCentralizerMatrix`: for every
  column `j` and Lie element `Y` of `T₀`, the Lie element `j₀ Y` lies in the
  Library's Lie centralizer `elementCentralizerLie G` of the Lie element with
  coordinates column `j`. Proof: the Library criterion
  `mem_elementCentralizerLie_iff_adjointDifferential`.

## After field extension

Here `E` is a field extension of `k`. `G_E` and the base change of `j₀` are
the Library scheme base changes along `algebraBaseMap k E`, and
`c.baseChange k E` are the induced Lie coordinates of `G_E`. A local instance
records that the structure morphism of `G_E` is affine, and a second one that
it is locally of finite type when that of `G` is.

- `tangentMatrix_targetMap_kernelFieldExtension`: for a Lie element `Y` of
  `T₀`, let `Y_E` be its scalar extension (`kernelFieldExtension`). Then the
  adjoint matrix of `j₀ Y_E` for `G_E` is the adjoint matrix of `j₀ Y` with
  entries mapped to `E`. Proof: `kernelFieldExtension_target`,
  `adjointRepresentation_baseChange_tangentMatrix` and naturality of tangent
  matrices.
- `exists_torusCentralizerMatrix_map_mulVec`: every vector over `E`
  annihilated by `ad(j₀ Y')` for all Lie elements `Y'` of the base change of
  `T₀` lies in the `E`-column space of `torusCentralizerMatrix c j₀`. Proof:
  it is in particular annihilated by the scalar extensions of the `k`-adjoint
  matrices, and `exists_mulVec_map_eq_of_commonKernel` applies.

## Main results

Assume moreover that `G` is smooth over `k` and that `T₀` is a torus.

- `denseRange_sliceMap_torusCentralizerMatrix`: the slice map
  `sliceMap (adjointRepresentation c) (torusCentralizerMatrix c j₀)` has
  dense range.

  Proof. Choose an infinite extension `Ω` over which `T₀` splits. Apply
  `exists_regular_targetMap` to `G_Ω`, the split torus `T₀,Ω` and the base
  change of `j₀`. This gives a Lie element `Y` of `T₀,Ω`. The coordinates of
  `j₀ Y` are annihilated by every `ad(j₀ Y')`, so they equal `B t₀` for some
  `t₀` over `Ω`. Here `B` is the centralizer matrix, and
  `exists_torusCentralizerMatrix_map_mulVec` applies. Every `v` over `Ω` is
  `ad(X) (j₀ Y) + z` with `z = B t'` by the same lemma. Transport `X` to a
  Lie element `ξ` of `G` over `Ω` with `kernelBaseChangeEquiv`. By
  `adjointRepresentation_baseChange_tangentMatrix`, `v` is
  `Ad-tangent(ξ) (B t₀) + B t'`. Now `denseRange_sliceMap_of_extension`
  applies.
- `exists_torusCentralizerSlice`: there are `r` and a matrix
  `B : Matrix (Fin d) (Fin r) k` such that `j₀ Y` centralizes every column
  of `B` for every Lie element `Y` of `T₀`, and the slice map
  `sliceMap (adjointRepresentation c) B` has dense range. Take
  `B = torusCentralizerMatrix c j₀`.

No hypothesis is placed on the field `k`, which may be finite. Irreducibility
of `G` is not assumed. The module proves dominance only; it does not prove
unirationality of any scheme.
