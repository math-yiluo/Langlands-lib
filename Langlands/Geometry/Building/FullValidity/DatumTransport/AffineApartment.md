# Axiom 4.1.4 under based group isomorphisms

Module `Langlands.Geometry.Building.FullValidity.DatumTransport.AffineApartment`.

## Purpose and provenance

Internal infrastructure for `KPBuildingDatumTransportStatement`: KP Axiom 4.1.4 (the affine
structure of the apartment) with its supplied splitting is preserved by the transport. The
proof follows the Library's same-group `ValuationBuildingAffineApartmentTransport`; the source
does not state this transport.

## Contents

- `DatumTransport.isSplitComponent_comp_iso`: a split component composed with an isomorphism is
  a split component.
- `ApartmentSplitting.basedTransport`: the same derived group `D`, derived torus `S'`, central
  torus `A_G` and torus `S' → D`; the derived inclusion becomes `d ≫ f`, the maps to `S` become
  `e ≫ σ` and `a ≫ σ`.
- `normalizingAut_basedTransport`: the automorphism of `S'` induced by `f(n)` is
  `σ⁻¹ ≫ Int(n) ≫ σ` (uniqueness of the normalizing automorphism).
- `normalizerAction_basedTransport`: the apartment comparison intertwines the actions of
  `n` and `f(n)`.
- `SatisfiesAffineApartmentAxiom.basedTransport`: derived subgroup and split component via
  composition with `f`; the complement `V(S') ⊕ V(A_G)` via `V(σ)`; the normalizer clause via
  the previous lemmas; central elements via `mem_center_comp_iso_iff`.
