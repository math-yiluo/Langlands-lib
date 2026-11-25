# Supplied dynamic quotient properness from independent affineness

This internal reduction constructs the actual closed comparison between two
supplied dynamic quotient schemes from a supplied affine homogeneous quotient
of the ambient group by the embedded subgroup. It also proves
`dynamicQuotientProper_of_reductiveLinearQuotientAffine`: the exact published
`ReductiveLinearQuotientAffineStatement` implies the exact published
`DynamicQuotientProperStatement`, in every universe and arbitrary
characteristic, retaining every supplied quotient and all relative scheme tests.
The affineness premise is an independent input to this module; it is proved
separately, as `reductiveLinearQuotientAffine` in
`Langlands.GroupScheme.Reductive.LinearQuotientAffineProof`.

For an arbitrary connected reductive group, the published linear embedding
reduction supplies a closed representation and an actual affine homogeneous
quotient of the general linear group by this subgroup, conditional on that
premise. The closed-product theorem applied to the supplied affine quotient
makes the product of the embedded subgroup with the ambient dynamic parabolic
closed. The general linear group has an actual proper dynamic quotient by the
published matrix argument. The actual comparison from the original supplied
quotient to that proper quotient is a closed immersion, with the original
projection equation. Its composite with the proper target structure morphism
is the original supplied structure morphism, which is therefore proper.

The provenance is internal composition of these actual morphism constructions.
No nontriviality, regularity or noncentrality assumption on the cocharacter is
made. The proof uses no excluded regular-cocharacter/Borel or rank-one value.
This is a conditional reduction and does not itself prove reductive linear
quotient affineness or `DynamicQuotientProperStatement` unconditionally. The
unconditional theorem `dynamicQuotientProper` in
`Langlands.GroupScheme.Dynamic.QuotientProperProof` combines this reduction
with `reductiveLinearQuotientAffine`.
