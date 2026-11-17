# Actual component and integral-frame maps

This is a derived prerequisite for Drinfeld, *Coverings of p-adic symmetric
regions* (1976), Section 2 A, printed p.109 (PDF p.3), final paragraph,
and printed p.110 (PDF p.4), opening paragraph, particularly condition (c).
The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The source supplies a rational frame r and compares determinant lattices
formed from the homogeneous components and from Pi-translates of r O^d.
This module constructs the integral sheaf maps whose images realize the
untranslated lattices. The sheafification and stalk comparisons are derived
constructions rather than separately asserted results in the paper.

All rings, modules and spaces share one universe. Let O be any commutative
ring, F an O-algebra field, X a topological space, and d a natural number.
There is no additional injectivity assumption on O → F. These constructions
do not require d to be nonzero.

`integralCoordinates` is the actual O-linear coordinate map O^d → F^d,
where the codomain uses restriction of scalars along O → F. It reuses
`integralCoordinateRangeMap` with the identity F-linear map.

For a `LatticePiSheaf M`, `componentToRational i` composes the actual
homogeneous inclusion M_i → M with the integral-to-rational sheaf unit.
`imageStalkMap_componentToRational` identifies its actual stalk map, followed
by the restriction-of-scalars stalk comparison, with the existing
`componentRationalStalkMap`. The proof is the stalk functor's composition
identity and the definitions of the two composites.

For a `FramedLatticePiSheaf M`, `integralFramePresheafMap` starts with the
constant integral vector presheaf. It applies `integralCoordinates`, the
sheafification unit of the constant F-vector presheaf, and the actual frame
followed by the rational degree-zero inclusion (`frameToTotal`). The last
two maps are restricted from F to O. Since its target is a sheaf,
`sheafifyLift` induces `integralFrameSheafMap` from the actual constant
O-vector sheaf to the scalar restriction of the total rational sheaf.
No comparison morphism is supplied as an input.

`integralFrameSheafMap_unit` proves the defining identity after precomposition
by the sheafification unit on every open. It is the corresponding component
of `toSheafify_sheafifyLift`. On the whole space, composing further with the
germ and the restriction-of-scalars stalk isomorphism gives exactly the
existing `integralFrameStalkMap`; this is
`integralFrameSheafMap_germ`. Its proof first uses the unit identity, then
the defining compatibility of `restrictionStalkIso` with germs, and finally
checks equality on each integral vector.

`imageStalkMap_integralFrameSheafMap_range` identifies the actual stalk image
of this sheaf map with `frameStalkLattice`, the existing r O^d. The proof
uses `constantSheaf_stalk_range`, which expresses the range of a map from
a constant sheaf in terms of its global constant vectors, then transports
that range through the restriction-of-scalars stalk isomorphism and applies
the germ identity just proved.

These are actual morphisms and images in module sheaves and their
neighborhood-colimit stalks. Finite generation, full rank, integral
injectivity, determinant normalization, its equivalence with a subsheaf
equality, and representability are not conclusions of this module.
