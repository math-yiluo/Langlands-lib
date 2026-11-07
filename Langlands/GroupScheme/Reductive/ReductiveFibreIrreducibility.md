# Reductive group schemes have geometrically irreducible fibres

Module `Langlands.GroupScheme.Reductive.ReductiveFibreIrreducibility`.

## Results

- `connectedSpace_residueFiber_of_geometricFiber`: for a group scheme `G` over `S` and a
  point `s`, the fibre `G ×_S Spec κ(s)` is connected if the geometric fibre over `s` is.
- `IsReductive.geometricallyIrreducible`: the structure morphism of a reductive group scheme
  is geometrically irreducible (Mathlib's `GeometricallyIrreducible`).

`OpenCellGluing` (`CellGluing.exists_iso_of_cellCompatible`) needs this property as an
instance hypothesis.

## Proof

1. The connectedness lemma. The geometric fibre is the pullback along
   `Spec κ(s)ᵃˡᵍ → Spec κ(s) → S`. Up to the canonical isomorphism
   `pullbackLeftPullbackSndIso`, its map to the residue fibre is a base change of the
   surjective morphism `Spec κ(s)ᵃˡᵍ → Spec κ(s)`, so it is surjective (Mathlib instance). A
   continuous surjection carries connectedness, so the residue fibre is connected.
2. By `GeometricallyIrreducible.iff_geometricallyIrreducible_fiber` it suffices to treat the
   residue fibres `G_s`. Each `G_s` is a smooth affine group over the field `κ(s)`. Smoothness
   and affineness are base changes of the hypotheses in `IsReductive`. `G_s` is connected by
   step 1, since `IsReductive.geometricFiber` gives connected geometric fibres.
3. The Library's `smoothConnectedAffineGeometry` shows that a smooth, connected, affine group
   over a field is geometrically integral. Geometric integrality gives geometric
   irreducibility.

## Provenance

This is the standard fact that a smooth connected group over a field is geometrically
irreducible: a rational point plus connectedness gives geometric connectedness (SGA3
VI_A 2.1.1, 2.4), and smooth plus geometrically connected gives geometrically irreducible.
The Library proves the field case as `smoothConnectedAffineGeometry`. This module only
transports it to the fibres.
