# Surjectivity of actual adjacent-rank normalized sections

This module is an internal consequence of the actual compact-section spanning
construction, the proved compact local-section theorem, compactness of the upper
parabolic quotient, and the character-twist and original-carrier induction
equivalences. It introduces no new literature theorem or analytic assumption.

In the general-field portion, the field is Hausdorff and topological, its
universe is independent of that of the original algebraic complex module, and
all natural ranks are retained. The inner measure is finite on compact sets,
positive on nonempty open sets, and preserved by right multiplication by the
actual lower large-block projection. The inner character has locally constant
complex values and the given representation is smooth. For the surjectivity
claims in this portion, compactness of the actual opposite-parabolic quotient
and a compact open subgroup basis are explicit hypotheses.

`adjacentRankLowerSectionTensor_unit_surjective` applies
`compactInclusion_bijective_of_compactSpace`: compact quotient makes every smooth
induced vector compactly supported modulo the parabolic. The preceding
`adjacentRankCompactSectionTensor_covers_compact` then writes that vector as the
image of a finite algebraic compact-test/vector tensor, with trivial outer
character. This is surjectivity on actual induced functions, before any scalar
coefficient map is applied.

The selected definition `adjacentRankLowerOuterTwistCoordinates` is the identity
linear equivalence on the original module. It intertwines the character twist
of the trivial-outer-character inducing action with the general-outer-character
action. This follows by multiplying their explicit unit-valued scalar factors.
`adjacentRankLowerOuterTwist` composes smooth induction's character-multiplication
equivalence with induction of those identity coordinates. Its evaluation formula
is exactly `theta(g) * f(g)`, interpreted as complex scalar multiplication on the
original module. `adjacentRankLowerOuterTwist_tensor` proves compatibility with
the complete rectangular tensor-section map by tensor induction. Consequently
`adjacentRankLowerSectionTensor_surjective` transports the trivial-character
surjectivity to every outer smooth character. No equality casts of
representation carriers or injectivity of a Whittaker coefficient map enter the
argument.

`Padic.oppositeParabolicQuotientCompact` discharges quotient compactness for
every actual block shape, every rank and every supplied p-adic topology. The
published `Parabolic.isCompact_integralRange` gives a compact set in the upper
quotient, and `Parabolic.quotientMap_image_integralRange` shows it covers that
quotient. Inverse transpose followed by projection to the opposite quotient is
continuous. Applying the upper cover to the inverse transpose of any element
and using `inverseTranspose_mem_oppositeParabolic_iff` proves that this compact
set's inverse-transpose image covers the opposite quotient. Thus the opposite
quotient is compact. This argument does not reverse block order or change the
inducing representations.

Finally `Padic.adjacentRankNormalizedSectionTensor_surjective` works over the
canonical p-adic topology with the exact `generalLinearHaar F.Carrier r` measure
and an arbitrary continuous quasicharacter. The existing
`generalLinearCompactOpen` construction supplies the required subgroup basis.
The measure's published compact-finiteness, open positivity and right Haar
invariance supply the measure hypotheses. The general surjectivity theorem is
specialized to the two precise normalized determinant characters from
`AdjacentRankNormalizedSection`. Inducing the inverse of
`adjacentRankLowerInducingCoordinates` then transports the surjective map to the
exact canonical normalized opposite induction with ordered blocks `(r+1,1)` and
original `Shahidi.pairCarrier V (ULift.{uV} Complex)` family. The composite is
definitionally the existing `adjacentRankNormalizedSectionTensor`.

The final theorem needs only smoothness of the original representation. It adds
no topology or norm on that module, no irreducibility, convergence, growth,
coefficient injectivity or Whittaker-type premise. Both field and original
carrier universes remain independent, and `r=0` is included. This module proves
full section spanning; Jacquet integrability, a common nonzero Whittaker
functional and whole model-image equality remain further obligations.
