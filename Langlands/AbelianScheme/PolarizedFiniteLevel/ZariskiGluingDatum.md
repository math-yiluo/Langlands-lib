# Gluing rigid ordinary polarized full-level data along an open cover

Setting as in `ZariskiGluingPolarization`.

## Declarations

Namespace `Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing`.

- `localLevel_compat`: the level sections of the transported local data agree on
  overlaps, as required by `ZariskiGluingLevel` (from the level equation of
  `overlapIso`, `hom_overlapIso_fst_fst` and `pullbackTuple_fst`).
- `gluedSections`, `pullbackTuple_gluedSections W`: the glued level sections restrict to
  those of `localTransport W`.
- `gluedDatum hU c hrig θ hdim hpol hdeg hfull : Datum P S g d n`: abelian scheme
  `gluedAbelian`, dual witness `gluedDualWitness`, polarization `gluedPolarization`,
  level sections `gluedSections`. The four propositional fields are explicit hypotheses:
  - `hdim`: relative dimension `g`;
  - `hpol`: `IsPolarization`;
  - `hdeg`: degree `d²`;
  - `hfull`: the full-level property.

  Each holds locally on `S`, and their local-to-global lemmas are proved in a separate
  module.
- `gluedDatumRestrictIso W : PolarizedIso ((gluedDatum …).pullback W.ι) (localTransport W)`,
  with the identity abelian isomorphism (`pullbackMap_gluedPolarization`,
  `pullbackTuple_gluedSections`).
- `isomorphic_gluedDatum_restrict W`: the restriction of the glued datum to `W` is
  isomorphic to `c W` (via `Datum.transportIso`).
- `isomorphic_restrict_of_subOpens`: for local data `a i` on the members of the cover with
  isomorphic restrictions to overlaps, any datum `b` on `S` whose restrictions to all
  small opens are isomorphic to `localDatum a W` restricts on each `U i` to a datum
  isomorphic to `a i`.

## Provenance

Internal: the existence half of the Zariski sheaf property of the moduli functor of
isomorphism classes of rigid data. Mumford, Fogarty and Kirwan (GIT, Chapter 7) obtain
the moduli space as a quotient instead; this gluing is the standard descent argument.
