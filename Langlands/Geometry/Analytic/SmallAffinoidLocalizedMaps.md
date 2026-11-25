# Full localized morphisms between small affinoid spectra

For a complete ultrametric normed field `K` and presented affinoid algebras
`R` and `S` with spectra small in universe `v`, `localizedMapEquiv R S`
identifies bounded `K`-algebra maps `R → S` with arrows from the localized
small spectrum of `S` to that of `R`. The underlying bounded map induces
the published `SmallAffinoidSpectrum.map` and then its image under
`localizationFunctor`. The field and spectrum universes are independent.
Trivial valuations and empty spectra are allowed.

The proof first checks the strong maps. The whole spectrum is a greatest
chart, and the published comparison says that `map` retains the original
bounded map there. A strong map between these presentations is determined
by its greatest-chart pullback. Transporting a given strong map's
pullback through the two greatest-chart algebra equalities therefore
gives its unique bounded representative.

The source-quotient Hom equivalence supplies a strong map on the
unchanged source for every arrow to a greatest-chart target. Faithfulness
of localization on strong maps proves that the bounded representative
is still unique. The composition formula uses the original strong
spectrum-map composition law and functoriality of localization.

## Provenance

The equivalence is derived from the published greatest-chart comparison,
small spectrum maps, and source-quotient Hom equivalence. It packages
complete bounded maps for use in descent of localized affinoid morphisms.
