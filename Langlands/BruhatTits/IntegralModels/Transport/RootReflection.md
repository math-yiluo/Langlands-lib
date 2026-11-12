# Transport of relative-root reflection data

Module `Langlands.BruhatTits.IntegralModels.Transport.RootReflection`.

## Purpose and provenance

This is internal infrastructure for the proof of
`Langlands.Geometry.Building.KPBuildingDatumTransportStatement`. The `rootDatum` field of a
supplied KP datum (Kaletha–Prasad §4.1, the root datum used in Axiom 4.1.22(6)) is a
`RelativeRootReflectionData i`. For each relative root `a` it gives a coroot pairing to `2`
with `a`, and a rational normalizer point acting on characters by the reflection formula
`χ ↦ χ - ⟨χ, a∨⟩ a`. The source does not state this transport separately.

## Construction

Let `e : T ≅ T'` and `f : G ≅ H` be isomorphisms over a field, and let `i ≫ f.hom = e.hom ≫ j`
(on underlying group schemes), with `i` and `j` monomorphisms. Let `ρ` be the actual bijection
`relativeRootsTransportEquiv e f h` from the relative roots of `i` to those of `j`; it
restricts `characterLattice.congr e`. Then `RelativeRootReflectionData.transport D e f h`
assigns to a root `a'` of `j`:

- the coroot `cocharacterLattice.congr e (D.coroot (ρ⁻¹ a'))`;
- the representative `normalizerPointsTransportEquiv e f h (D.representative (ρ⁻¹ a'))`,
  that is, the old normalizer point followed by `f`.

`pair_self` follows from `latticePairing_congr`. The reflection formula follows from
`weylAction_transport` (the Weyl actions intertwine with `characterLattice.congr e`), from
the old formula, and from additivity of `characterLattice.congr e`.

`transport_coroot` and `transport_representative` state the values at `ρ a`.
