# Chartwise projections from quotient chart systems to affinoid atlases

`AffinoidChartSystem.AtlasProjection C a` packages the maps and identities
relating an actual quotient chart system `C` over one complete ultrametric
field to an indexed affinoid atlas `a` over another such field. There is no
assumed relation between the fields.

The data are an equivalence of chart indices, a continuous map from the
already constructed quotient `C.Space` to the original space, and continuous
maps between corresponding spectra. The maps commute with the charts. A
quotient chart range is exactly the inverse image of the corresponding
original range, and every original chart containment gives an inclusion in
the chart system. No embedding, local Hausdorffness, or net property of the
quotient is included as a field. No new glued space is supplied as input.

This is internal topological infrastructure for the ground field extension
construction motivated by Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), §1.4, printed page 30 (PDF page 27), and the atlas
conventions of §1.2, printed pages 16–18 (PDF pages 13–15). This packaging is
derived content; the source does not define this Lean structure.

The two field universes, the base space universe, and both index universes
are independent. Empty index types and empty spectra are allowed.
