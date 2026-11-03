# Geometry from natural vector coordinates

This derived unit uses the published actual vector group and the fully faithful
group-valued Yoneda construction. It does not classify any previously given
unipotent group.

For any commutative base ring `R`, `vectorCoordinatesIso` converts a family of
multiplicative equivalences between the points of an actual group scheme `V`
and additive tuples of `n` global functions into a group-scheme isomorphism
`V ≅ VectorGroup.groupScheme R n`. The required naturality ranges over every
scheme over `Spec R`. Compose each supplied equivalence with the inverse of the
standard vector-group coordinates and apply the existing `isoOfPoints`.
Coordinate naturality proves naturality of this composite.

The published `VectorGroup.smoothOfRelativeDimension` proves that the standard vector group has smooth relative dimension `n`: its coordinate
algebra is the polynomial algebra in `Fin n`, which is standard smooth of that
relative dimension. The ring-to-scheme smoothness comparison gives the claim.
Transport along `vectorCoordinatesIso` then proves
`IsVectorGroupOfDimension.smoothOfRelativeDimension_overRing` and
`IsVectorGroupOfDimension.isAffineHom_overRing`.

Finally, `IsVectorGroupOfDimension.pos_of_range_ne_bot_overRing` proves `0 < n` whenever
a morphism from `V` has a nontrivial actual image. If `n = 0`, the supplied
coordinates make the point group of `V` trivial on every test scheme. Every
point of the image is consequently the unit, contradicting nontriviality. This
argument needs neither a field nor a smoothness assumption.

These are conditional consequences of natural coordinates. Existence of such
coordinates on smooth commutative unipotent groups, positive-characteristic
torus linearization, and the exact ordered-product theorem remain separate
obligations. The imported mathematical constructions retain their authorship.
