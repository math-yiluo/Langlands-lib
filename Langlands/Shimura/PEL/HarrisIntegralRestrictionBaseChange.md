# Supplied integral data on actual Harris pointed pullback

This internal construction concerns the already published actual
`levelDataBaseChange` of Harris positive polarized representatives. The original
Harris level and actual abelian schemes are retained, and the source level orbit
supplies the frame used by that construction. The positive auxiliary left
involution, all dual evaluation inputs, tensor and Picard prerequisites,
polarization stability and dual naturality remain those of the published
construction. Integral restrictions remain supplied on the source objects.

`levelDataIntegralRestrictionBaseChange` applies actual abelian-scheme base
change to every endomorphism of a supplied integral Harris-order action.
Agreement with the existing changed rational action follows from agreement
on the source and compatibility of rationalization with base change. The
changed action object is exactly the one used by `levelDataBaseChange`.

`levelDataIntegralIsoBaseChange` transports any supplied exactly equivariant
integral representatives of the original rational action isomorphism. It uses
the existing equivariant integral-data base-change construction, so both
nonzero denominators are unchanged and the actual maps are their actual base
changes. The rational action isomorphism is the image of the original one
under `RationalAlgebraAction.pullback`.

`levelDataIntegralPolarizationBaseChange` transports supplied exact integral
polarization cross-multiple data for that same integral representative. The
canonical dual comparisons are exactly the ones in the actual Harris changed
polarizations. The previously proved `integralDualMultipleDataBaseChange`
gives the equation and preserves its left and right integer witnesses and
prescribed rational ratio. The unchanged forward denominator identifies that
ratio with its square times the original rational multiplier.

`levelDataIntegralPolarizedMultiple_baseChange` packages these two transports
to preserve the existing exact integral multiple proposition with the original
multiplier and the mapped original rational isomorphism. Its proof destructs
the supplied witnesses and applies the two constructors above.

This is transport of supplied data on actual representatives. It does not
claim existence of integral restrictions for arbitrary rational actions,
reflection under base change, equality with independently chosen integral
data, independence of geometric points or existence of a moduli scheme.
