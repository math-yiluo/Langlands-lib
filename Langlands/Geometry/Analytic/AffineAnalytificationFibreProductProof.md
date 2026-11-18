# Affine analytification carries tensor products to fibre products

`affineAnalytificationFibreProduct` proves the Library's
`AffineAnalytificationFibreProductStatement.{u, v, w, x}` in its four
independent universes. It proves the affine case of the compatibility
with fibre products in Berkovich 1993, Proposition 2.6.1, for the
polynomial-locus models and induced morphisms named by the statement.

The tensor lift of a compatible pair of algebra maps into a source chart
commutes with restriction to a smaller chart. Applying this to the families
extracted from two commuting strong morphisms produces a compatible family
of algebra maps from the relative tensor product. The agreement over the base
algebra follows by extracting the two equal composites of the cone.

`algebraFamilyData` chooses an original target chart and bounded pullback
on each source chart. `saturatedChartHom` transports this data to the
saturated target and reconstructs a complete strong morphism. Extraction
of the reconstructed morphism recovers the tensor family on each chart.
Its projections recover the given morphisms by the tensor inclusion
identities and faithfulness of chart-family extraction. The identity
quasi-isomorphism supplies refined existence. If two strong morphisms
have equal projections, their extracted maps agree on both tensor
inclusions and therefore on the entire tensor product on every chart.
Faithfulness identifies the morphisms.

Contravariant functoriality and the equality of the two inclusions of
`C` into `A ⊗[C] B` give the commuting square.
`IsRefinedStrongPullback.isPullback` uses the established right-fraction
construction to supply existence and uniqueness for arbitrary localized
cones.
