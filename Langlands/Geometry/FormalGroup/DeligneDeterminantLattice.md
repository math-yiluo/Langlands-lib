# Stalk lattices for the framed determinant normalization

This is a derived prerequisite for Drinfeld, *Coverings of p-adic symmetric
regions* (1976), Section 2 A, printed p.109 (PDF p.3), final paragraph,
and printed p.110 (PDF p.4), opening paragraph, especially condition (c).
The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The source compares the determinant of eta^i with
pi^(-i) wedge^d(Pi^i r O^d) on S_i, for every integer i. The framed
lattice on the right is the image of O^d under the actual frame r.

For a commutative ring O, an O-algebra field F, and a topological space X,
`restrictionStalkIso` identifies the O-module stalk of an F-sheaf after
scalar restriction with scalar restriction of its F-module stalk. It uses
the fact that restriction of module scalars preserves the neighborhood
colimit that actually defines the stalk. This is a restriction-of-scalars
comparison, not a tensor/stalk comparison.

`integralRationalStalkMap` takes the stalk map of the already constructed
integral rationalization unit and follows it by this comparison.
`integralRationalStalkMap_germ` proves that it sends a germ to the germ
of the corresponding actual integral-to-rational section. The proof uses
naturality of stalk maps on germs and the colimit comparison's defining
identity.

For nonzero d and any actual O[Pi]-module sheaf, `rationalLatticeStalk`
is the F-module stalk of its total rational sheaf. For a `LatticePiSheaf`,
`rationalInclusion` rationalizes the actual homogeneous inclusion.
`componentRationalStalkMap` first maps the integral component stalk into
the integral total stalk, then applies `integralRationalStalkMap`.
`componentStalkLattice` is its O-linear range in the total rational stalk.
The word lattice here names this constructed O-submodule; finite generation,
full rank, and injectivity of the integral map are not conclusions of this
module.

For `FramedLatticePiSheaf`, `frameToTotal` follows the actual frame by
the rationalized degree-zero inclusion. `frameStalkMap` sends a vector
in F^d to the corresponding constant global section through the constant
presheaf's sheafification unit, and then takes its germ after applying
`frameToTotal`. `integralFrameStalkMap` first maps O^d into F^d using
the actual algebra map, and is proved O-linear. Its range,
`frameStalkLattice`, is the actual r O^d in the total rational stalk.
No arbitrary comparison map or unrelated lattice is supplied as input.

For an F-module V and an O-submodule L of its scalar restriction,
`exteriorStalkLattice k V L` is the O-span of all actual exterior
products v_1 wedge ... wedge v_k, with each v_j in L, in wedge_F^k V.
`scaleStalkLattice` takes the image under actual scalar multiplication
on V, restricted to an O-linear map.

Under the additional hypothesis that the image of pi in F is nonzero,
`rationalPiStalkAut` takes the stalk of the constructed total rational
Pi automorphism. `translatedFrameStalkLattice` takes the O-linear image
of r O^d under its n-th power for any integer n, including negative
integers. `normalizedFrameDeterminant` then takes the d-fold exterior
lattice and multiplies it by the F-scalar (image pi)^(-n). Thus scaling
takes place after forming the exterior products, as in the source.

For actual `SheafPreDatum` on a scheme S, `componentDeterminant` takes
the d-fold exterior lattice of `componentStalkLattice`. The proposition
`DeterminantNormalized` asks for equality with
`normalizedFrameDeterminant` at every point of S_(n mod d), for every
integer n. The locus is the previously constructed actual zero set of
Pi on the residue-field fibre of the homogeneous tangent sheaf.
All rings, spaces and modules use the common universe of the preceding
Deligne modules. No finite range of integer representatives replaces
this quantifier.

The derived provenance is the concrete composition of stalk colimits,
the actual integral and frame maps, O-linear ranges, actual exterior
products, and integer powers of an already constructed automorphism.
This module defines the resulting stalkwise normalization predicate.
It does not prove integral injectivity, a tensor/stalk comparison, or
equivalence to an independently constructed exterior-power subsheaf
equality. It does not impose conditions (a) or (b), construct
isomorphism classes, base change or the PGL action, or prove
representability or a generic-fibre comparison.
