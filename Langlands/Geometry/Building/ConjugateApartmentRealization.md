# Realizing a conjugate valuation apartment in the original quotient

Author: Worker 118.

Let `g ∈ G(k)` and `e : S ≅ S'` be actual isomorphism data satisfying the
conjugation square for the inclusions `i` and `j`. Work over an arbitrary
field, with both underlying inclusions monomorphisms, an affine ambient
structural morphism, and supplied `D : KPApartmentData i ω`.
The target data are exactly `D.transport e (G.innerIso g) h`.

`D.conjugateReducedBuildingEquiv e g h` identifies their reduced quotient with
the original quotient `D.ReducedBuilding`. First apply the inverse of the
existing cross-torus quotient equivalence, then act by the original rational
point `g`. Its inverse first acts by `g⁻¹`, then applies the cross-torus
quotient equivalence. The two inverse laws follow from the original action
and equivalence laws.

This identification intertwines the same original `G(k)`-actions on both
quotients. Indeed, cross-torus transport twists an acting point by actual
inner conjugation. After taking its inverse, acting by `g` cancels that
twist: `g*(g⁻¹*u*g) = u*g`. The proof uses the original rational-point
inner-automorphism formula and the established quotient equivariance.

`D.conjugateApartmentMap e g h` realizes the actual target valuation apartment
in the original quotient through this equivalence. At a transported source
point its value is exactly `g • D.apartmentMap x`. Thus its image is the
translate by `g` of the original apartment image. It is injective exactly
when the original apartment chart is injective. The already constructed
affine map between the valuation apartments has the actual torus-induced
quotient derivative; this realization identifies it with the prescribed
action of `g` on the quotient.

The original target normalizer action is compatible with this realization
through its actual rational points in the same quotient. Full stabilizers
of corresponding quotient points are equal as subgroups of the same
`G(k)`. This asserts no equality between full fixers, parahorics and
zero/one intersections.

The provenance is internal: the actual cross-torus quotient equivalence,
the original group action, the original chart and the inner-automorphism
point identity give these constructions. No building axiom is assumed.
The source and target quotient types are not asserted to satisfy abstract
building validity. Global assignment to actual maximal split tori,
independence from the choice of transporter, compatibility with separately
chosen canonical classes, apartment intersections, full A2 and general
building existence remain separate obligations.
