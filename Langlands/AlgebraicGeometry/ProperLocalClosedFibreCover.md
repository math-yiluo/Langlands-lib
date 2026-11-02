# Total covers from a closed fibre over a local ring

This module derives an actual scheme open cover from neighbourhoods of the
closed fibre. It also constructs a common point of every total open meeting
the closed fibre of a smooth geometrically connected morphism. The content
is internal: it combines Mathlib's topology of local spectra, closed images,
scheme fibres and open covers with the Library theorem
`Langlands.AbelianScheme.smoothGeometricIntegrality`.

Let `R : Type u` be a commutative local ring, let `X : Scheme.{u}`, and let
`p : X ⟶ Spec R`. No domain, valuation, rank, finite type or Noetherian
assumption on `R` is imposed.

## The total cover

For a universally closed `p`,
`open_eq_top_of_contains_closedFibre` proves that an open `U` containing
every `x` with `p x = IsLocalRing.closedPoint R` is the whole source.
The proof assumes a point lies outside `U`. The image of the closed
complement is closed and contains that point's image. Every point of a local
spectrum specializes to its closed point, so the image also contains the
closed point. A preimage in the complement contradicts the hypothesis on `U`.
Universally closed is the exact hypothesis; in particular, the result applies
to proper morphisms.

`iSup_eq_top_of_covers_closedFibre` applies this to the union of a family of
opens, allowing the indexing type to have any universe `v`.
`iSup_eq_top_of_closedFibre_neighbourhoods` indexes by the actual
scheme-theoretic closed fibre `p.fiber (IsLocalRing.closedPoint R)`.
It uses `Scheme.Hom.range_fiberι` to pass between that fibre and the
set-theoretic inverse image of the closed point.

`closedFibreNeighbourhoodCover p U hU` is an actual `X.OpenCover`.
Its inputs are a total open `U x` for each point `x` of the scheme-theoretic
closed fibre and a proof that the image of `x` belongs to `U x`.
It calls `Scheme.openCoverOfIsOpenCover` with the proved union equality.
It makes no finiteness assertion about this cover.

## A common point

`integral_fibre_of_smooth_geometricallyConnected` applies to every fibre of
a smooth geometrically connected `p`. This lemma does not require `R` to be
local. Smoothness and geometric connectedness pass to the morphism from
the fibre to the spectrum of its residue field. The imported field theorem
gives geometric integrality, and hence integrality of the fibre itself.

For local `R`, `closedFibreGenericPoint p` is the image in `X` of Mathlib's
chosen generic point of this integral closed fibre.
`closedFibreGenericPoint_spec` proves that it is a generic point of the
set-theoretic closed fibre. The generic-point image lemma first gives the
closure of the image of the whole fibre. This image is exactly the
set-theoretic closed fibre and is already closed, since the closed point of
the local spectrum is closed.

`closedFibreGenericPoint_mem` uses the generic-point criterion for open sets:
every total open meeting the closed fibre contains this chosen point.
Universal closedness is not needed for these common-point results.

These constructions are prerequisites for the valuation line-bundle extension
argument. They do not construct normalized generic frames, extend transition
units, or prove `ValuationRingTwoAxisExtensionStatement`.
