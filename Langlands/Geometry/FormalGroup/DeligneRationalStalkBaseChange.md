# Actual rational stalk comparisons for Deligne lattices

This module constructs the canonical comparison between the actual total rational
stalk of a Deligne lattice at an image point and the actual total rational stalk
of its inverse image. It proves that this comparison preserves the integral
stalk map and carries each actual homogeneous component image to its pulled
component image.

## Source and scope

The source motivation is V. G. Drinfeld, *Coverings of p-adic Symmetric Regions*
(1976), Section 2 A, printed pages 109–110 (PDF pages 3–4), the preliminary sheaf
data at the end of page 109 and condition (c) in the opening paragraph of page
110. The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.

Drinfeld's condition compares determinant lattices inside rational eta, using
the integral homogeneous components and the rational frame. The present
comparison results are derived infrastructure for that condition, not a separate
assertion quoted from the paper. The constructed rationalization,
`integralRationalStalkMap`, and `componentStalkLattice` are the existing Library
objects; no comparison is supplied as additional data.

This unit does not prove compatibility of the rational frame or of integer Pi
powers, preservation of determinant normalization, injectivity of the integral
map, or equality with a separately constructed exterior-power subsheaf. Full
admissibility and representability remain separate obligations.

## Parameters and actual objects

The generic coefficient-unit identity has commutative rings `O` and `R` in the
same universe, a unital ring map `rho : O -> R`, topological spaces `X` and `Y`,
and an arbitrary continuous map `f : X -> Y`. For rationalization, `F` is a field
with an `O`-algebra structure. No locality, flatness of `f`, nilpotence, or
local-field hypothesis is used.

Write `P_O` and `P_F` for the existing actual sheaf inverse-image functors and
`Q_X` for `rationalSheafFunctor F X`, which extends coefficients on sections
and then sheafifies. For an `O`-module sheaf `M` on `Y` and `x` in `X`,
`rationalStalkPullbackIso` is the F-linear isomorphism

    (Q_Y M)_(f x)  ->  (Q_X (P_O M))_x.

It composes the existing actual inverse-image stalk isomorphism with the stalk
of `inverseImageRationalIso`. It is therefore a comparison of the neighborhood
colimits of the sheaves themselves, not a chosen tensor presentation of a stalk.

For any natural number `d`, coefficient `pi : O`, and sheaf `M` of modules over
the existing `PiAlgebra d pi`, `inverseImageRationalLatticeIso` composes
`inverseImageRationalIso` on the scalar-restricted sheaf with rationalization of
`inverseImageLatticeScalarIso`. Thus it compares

    P_F (rationalLattice F Y d pi M)
      -> rationalLattice F X d pi (P_(PiAlgebra) M).

`rationalLatticeStalkPullbackIso` applies the existing inverse-image stalk
comparison and the stalk of this sheaf comparison. It retains the F-module
structure. These two definitions require no `NeZero d` assumption. For the final
component statements `d` is nonzero and `M : LatticePiSheaf d pi Y` is the
existing flat graded lattice structure, with its actual components and inclusions.

## Unit, germ and naturality identities

`inverseImageExtensionIso_unit_section` states that, on every section of `M`,
the existing extension/inverse-image comparison takes the extension unit
followed by the inverse-image unit to the inverse-image unit followed by the
extension unit. Its proof uses `homEquiv_leftAdjointUniq_hom_app` for the two
composite adjunctions and evaluates their unit identity on the section.
`inverseImageRationalIso_unit_section` specializes this to `O -> F`, using the
existing equality of `rationalUnit` with the coefficient adjunction unit.

`rationalStalkPullbackIso_germ` computes the rational comparison on every germ
by the inverse-image unit, followed by the rationalization comparison, followed
by the actual target germ. It follows from the previously proved
`inverseImageStalkIso_germ` and naturality of germs under a presheaf map.

`rationalStalkPullbackIso_integral` proves the commutative square whose top map
is `integralRationalStalkMap` at `f x`, whose bottom map is that map for `P_O M`
at `x`, whose integral side is `inverseImageStalkIso`, and whose rational side
is the O-scalar restriction of `rationalStalkPullbackIso`. Stalk homomorphisms
are compared on all germs. The germ formulas reduce the square to the composite
unit identity just proved.

`integralRationalStalkMap_naturality` proves naturality of the integral stalk map
in every actual `O`-sheaf morphism. Its proof compares germs and applies
`rationalUnit_naturality`. `rationalStalkPullbackIso_naturality` proves naturality
of the rational comparison in every such morphism, using naturality of
`inverseImageStalkIso` and `inverseImageRationalIso`.

## Total lattice and component compatibility

`rationalLatticeStalkPullbackIso_hom` expresses the total rational comparison
as `rationalStalkPullbackIso` on the scalar-restricted sheaf followed by the
stalk of rationalization of `inverseImageLatticeScalarIso`.
`rationalLatticeStalkPullbackIso_integral` consequently commutes with the actual
total integral-to-rational maps. On the integral side it uses
`inverseImageStalkIso` followed by the stalk of
`inverseImageLatticeScalarIso`. The proof combines the generic integral square
with naturality of the integral stalk map.

`LatticePiSheaf.componentRationalStalkMap_pullback` states the corresponding
square for every component `i : ZMod d`: the integral side is the actual
inverse-image stalk isomorphism for `M.component i`, the rational side is the
O-scalar restriction of `rationalLatticeStalkPullbackIso`, and the other two
sides are the existing `componentRationalStalkMap` maps. The proof combines the
total integral square with naturality for the actual component inclusion. The
pulled inclusion is precisely the inverse image of the original inclusion
followed by `inverseImageLatticeScalarIso`, as in the existing construction of
`LatticePiSheaf.inverseImage`.

`LatticePiSheaf.componentStalkLattice_pullback` states that mapping the actual
component O-submodule by this restricted F-linear comparison gives exactly
`(M.inverseImage f).componentStalkLattice F i x`. The proof uses representatives
of each linear-map range, the preceding square, and surjectivity of the actual
inverse-image component stalk isomorphism for the reverse containment. It does
not require or assert that either integral-to-rational map is injective.
