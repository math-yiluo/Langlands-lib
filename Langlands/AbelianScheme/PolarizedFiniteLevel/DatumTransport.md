# Transport of ordinary polarized full-level data along isomorphisms

This module moves a whole datum `Datum P S g d n` along an isomorphism of abelian
schemes. It uses Worker 5600's `DualWitness.isPolarization_iso_transport` (module
`PolarizationIsoTransport`) for the polarization.

## Declarations

- `Datum.transport b e W`: for a datum `b : Datum P S g d n`, an abelian scheme `A` over
  `S`, an isomorphism `e : A ≅ b.abelian` and any dual witness `W : DualWitness A`, the
  datum with
  - abelian scheme `A`;
  - dimension: `A` has relative dimension `g`;
  - dual witness `W`;
  - polarization `e.hom ≫ b.polarization ≫ W.map P b.dualWitness e.hom`;
  - polarization predicate, degree `d²` and level sections `b.level.mapIso e.symm`, all
    transported from `b`.
- `Datum.transportIso b e W : PolarizedIso (b.transport e W) b`, whose abelian
  isomorphism is `e`.

## Proofs

- Dimension: `A.X.hom = hom e.hom ≫ b.abelian.X.hom` (the isomorphism is over `S`), and
  smoothness of relative dimension `g` respects isomorphisms
  (`MorphismProperty.cancel_left_of_respectsIso`).
- Polarization predicate: `DualWitness.isPolarization_iso_transport`.
- Degree: `HasDegreeSquare.post_iso` along the dual comparison
  `W.mapIso P b.dualWitness e`, then `HasDegreeSquare.pre_iso` along `e`. The needed
  isogeny is `b.polarized.1` composed with `isIsogeny_of_iso`.
- Level: `FullLevel.mapIso` along `e.symm`.
- `transportIso`: the polarization equation of `PolarizedIso` holds by definition. The
  level equation is `apply_symm_apply` of the linear equivalence `levelIsoLinear e`, whose
  inverse map is the level map of `e.inv`.

## Provenance

Internal bookkeeping. Every field is transported along the isomorphism with the
Library's existing API and the polarization transport above. There is no literature
content beyond that of the transported structures.
