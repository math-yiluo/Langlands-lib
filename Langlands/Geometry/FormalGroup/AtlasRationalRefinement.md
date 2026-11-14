# Restriction of rational formal atlas maps to finer covers

This is internal infrastructure derived from the implemented integral refinement
and rational atlas Hom constructions. It introduces no new assertion from the
original literature.

The commutative rings O and R have an O-algebra structure on R, and F is a field
with an O-algebra structure. Coordinate types are finite and may differ between
atlases. Tests are R-algebras in the universe of R. The original covers are equal;
a refinement supplies a new principal cover and actual localization containments
in selected original charts.
`CoverRefinement.opens_eq_retarget` records that retargeting the selected source
charts leaves this finer cover unchanged.

`Hom.restrictLinear` packages the existing formal `Hom.restrict` as an O-linear
map. The restriction conjugates each original formal homomorphism by the two
actual identity-coordinate coefficient comparison isomorphisms. Bilinearity of
formal composition proves additivity and scalar linearity. This uses the formal
target group law and O-action, including when coordinate addition is nonlinear.

`RationalHom.restrict` extends that linear map by F-scalars. On a simple tensor
it sends a tensor f to a tensor (f restricted to the refinement); hence it sends
the canonical rationalization of an integral map to the rationalization of its
restriction. Tensor induction, together with the integral restriction equations,
proves preservation of identity and composition. In the latter equation the
second map is restricted along the refinement retargeted to the intermediate
atlas. `restrictRingHom` packages restriction of endomorphisms as a ring map for
the actual formal composition multiplication.

`onChart_restrict` proves the formal comparison square in coordinate rational
Hom. Evaluation of the restricted map equals the composite of the source
coefficient comparison, evaluation in the chosen original chart, and the inverse
target coefficient comparison, in that order. Its proof uses additivity to
reduce to simple tensors, where the equation is the defining integral
restriction and multiplication by the unit scalars. Thus the equation retains
the actual formal maps, not just a relation between point functions.

With O a domain and F its fraction field, `QuasiIsogeny.restrict` restricts both
rational maps. Preservation of composition and identity proves their two inverse
equations. Restriction preserves identity quasi-isogenies, reversal, composition,
and inclusion of integral isomorphisms. The forward and reverse maps remain
exactly the corresponding rational restriction maps; extensionality in the
forward map proves these compatibility laws.

The objects here remain global finite tensor sums of integral atlas maps.
Restriction produces maps on the selected finer cover; it does not assert
injectivity, surjectivity, independence of source selections, or an identification
with all locally rational maps. Full-order equivariance, general local gluing,
heights, framing, moduli functors and representability are separate constructions.
