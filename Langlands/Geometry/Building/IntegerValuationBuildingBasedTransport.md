# Integer-valued building data under based group isomorphisms

Module `Langlands.Geometry.Building.IntegerValuationBuildingBasedTransport`.

## Setting

Let `k` be a field with a valuation `v : Valuation k ℤₘ₀`, let `f : G ≅ H` be an
isomorphism of affine group schemes over `k`, let `B : IntegerValuationBuildingData v G`,
and let `σ : B.S ≅ S'` be an isomorphism of commutative group schemes together with a
morphism `j : S' → H` such that `B.i ≫ f.hom = σ ≫ j` (the square `h`).

## Contents

* `IntegerValuation.IsCentralizerCompatible.transport_basedIso` and
  `IntegerValuation.IsOmegaCompatible.transport_basedIso`: the integer-valued axiom V 6
  of Kaletha–Prasad Definition 6.1.2 (the centralizer acts on a valuation of the root
  datum by the translation `-ω_Z`) is preserved when the root-function family is carried
  through `(σ, f)` (`RootFunctionFamily.transportEquiv`), for any centralizer datum of the
  target torus. The proof compares the two centralizer representatives by the canonical
  isomorphism of representing objects and shows that the integer centralizer translation
  commutes with the cocharacter isomorphism `cocharacterRealCongr σ`. This is the
  integer-valued copy of the Library's local-field `IsCentralizerCompatible.transport_basedIso`.
* `IntegerValuationBuildingData.isMaximalSplitTorus_of_basedIso`: `j` is a maximal split
  torus of `H`.
* `IntegerValuationBuildingData.basedTransport`: building data of `H` with torus exactly
  `j`: apartment class `B.apartment.transport σ f h` (the image of the source class),
  centralizer `B.centralizer.basedTransport σ f h`, and V 6 from the previous item. It is
  the integer-valued analogue of `ValuationBuildingData.basedTransport`.
* `basedApartmentEquiv` and `basedBuildingEquiv`: the affine comparison of apartments and
  the comparison `B(G) ≃ B(H)` of reduced buildings (KP (7.6.2)), given by the Library's
  `apartmentTransportAffineEquiv` and `reducedBuildingTransportEquiv`.
* `basedBuildingEquiv_smul` (equivariance along `f`), `basedBuildingEquiv_apartmentMap`.
* `map_fixer_basedTransport` and `map_oneStabilizer_basedTransport`: the image under `f`
  of the fixer, respectively of the one-group stabilizer `G(k)^1 ∩ G(k)_y`, of a point
  `y` is the fixer, respectively one-group stabilizer, of the transported point.
* `transportedRoots_basedApartmentEquiv`: the affine roots of the target apartment are the
  transported affine roots.
* `isSpecialPoint_basedTransport_iff`: special points of the reduced building are
  preserved and reflected.

## Provenance

Internal transport infrastructure: no new mathematical definition. Every construction is
the transport of existing Library data along the given isomorphisms, needed to move
supplied building data to the coordinate torus of a split model.
