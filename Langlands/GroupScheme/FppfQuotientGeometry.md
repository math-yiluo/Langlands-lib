# Connected fibres and connected inverse images of fppf quotient maps

This internal helper unit proves topological connectedness facts for a group
scheme homomorphism `q : G ⟶ Q` whose actual kernel is geometrically
connected. It supplies the connectedness step in the proof of
`UnipotentQuotientSplitTorusPreimageStatement`, where the inverse image of a
connected closed subgroup under a quotient by a connected unipotent subgroup
must be connected.

## Statements

All declarations live in `Langlands.GroupScheme.FppfQuotientGeometry`.

- `connectedSpace_of_isEmbedding`: for topological spaces `X` and `Y` and a
  topological embedding `f : X → Y` whose range is a connected subset of `Y`,
  the space `X` is connected. This is a general point-set fact.

The remaining statements work over an arbitrary base scheme `S : Scheme.{u}`,
with group schemes `G Q : GroupScheme S` and a homomorphism `q : G ⟶ Q`.
`kernel q` is the actual kernel group scheme from `Langlands.GroupScheme.KernelPair`
(the base change of `q` along the unit of `Q`).

- `geometricallyConnected_fst_kernel`: if `(kernel q).X.hom` is geometrically
  connected, then so is the underlying scheme morphism of the first projection
  `G.X ⊗ (kernel q).X ⟶ G.X`. This is base change of geometric connectedness.
- `isConnected_preimage_singleton`: if `(kernel q).X.hom` is geometrically
  connected and the underlying scheme map of `q` is surjective, then every
  fibre `q⁻¹{y}` (as a subset of the underlying space of `G.X.left`) is a
  connected set.
- `isConnected_preimage`: if additionally the underlying scheme map of `q` is
  flat and locally of finite presentation, then for every connected closed
  subset `s` of the underlying space of `Q.X.left`, the inverse image `q⁻¹ s`
  is connected.

No quotient-functor hypothesis such as `IsFppfQuotient` is required; only the
listed properties of the underlying scheme morphism and of the kernel.

## Provenance and proof

These are standard facts. The formal route is an internal derivation from:

- `KernelPair.action` and `KernelPair.isPullback_scheme` in
  `Langlands.GroupScheme.KernelPair`: the square with legs the projection
  `G ⊗ ker q ⟶ G` and the action map `(g, v) ↦ g · v`, over `q` on both
  sides, is a pullback of schemes;
- Mathlib's `Scheme.Hom.isConnected_preimage_singleton` (fibres of a
  geometrically connected morphism are connected),
  `Scheme.image_preimage_eq_of_isPullback`, and
  `Topology.IsCoinducing.isConnected_preimage_of_isClosed`;
- Mathlib's `Scheme.Hom.isOpenMap` for universally open morphisms, with the
  instance making flat morphisms locally of finite presentation universally
  open.

For a fibre over `y`, choose `x` with `q x = y` by surjectivity. The fibre of
the projection over `x` is connected because the projection is geometrically
connected. By the pullback square, the image of this fibre under the action map
is exactly `q⁻¹{q x}`, so the fibre of `q` is a continuous image of a connected
set.

For a connected closed subset `s`, the flat, locally finitely presented,
surjective `q` is an open surjection and hence a quotient map. A quotient map
with connected fibres has connected inverse images of connected closed sets,
which is Mathlib's `isConnected_preimage_of_isClosed`.

For `connectedSpace_of_isEmbedding`, nonemptiness of the range gives a point of
`X`, and an embedding maps `univ` to its range with preconnectedness reflected.

Worker 1390 authored this unit.
