# Actual integral points of canonical restricted unitary models

This derived unit identifies the actual integral-point image of the
canonical restricted unitary charts and lattice models. It composes the
section square in `IntegralModel.AffineWeilPoints` with the published
unitary coordinate and lattice membership theorems. Its provenance is
internal specialization of those results.

Let `A` and `O` be commutative domains with fraction fields `F` and `K`,
respectively, and suppose that `O` is finite projective over `A`.
The specified `A`-algebra maps to `K` through `O` and through `F` must
agree. Let `L / K` be a separable quadratic extension. All types lie
in an arbitrary common universe `u`. No localness or unramifiedness
assumption on `A` is required.

In the namespace `SU3Root.IntegralChart`,
`canonicalWeilRationalPointsEquiv` is a multiplicative equivalence
from rational points of `canonicalWeilGroup A F O K L`, the actual
restriction of the unitary parameter group from `K` to `F`, to
`rationalParameters K L`. It composes the generic restriction section
equivalence with the existing `unitaryRationalPointsEquiv K L`.
It is independent of a choice of integral chart.

For an integral chart `C` with a finite index type `I`,
`C.canonicalWeilIntegralCoordinatesEquiv` identifies integral sections
of `C.canonicalWeilModel` with `BilinearCoordinate.Coordinates C.coeff`.
It composes the actual model section equivalence with the original
chart's `integralCoordinatesEquiv`.

`canonicalWeilRationalPointsEquiv_integralPointMap` evaluates the
actual integral-point map. If the integral section has vector
coordinates `a : I → O` and scalar coordinate `b : O`, its image
under the generic parameter equivalence is

`fieldPoint C.data (fun i => algebraMap O K (a i)) (algebraMap O K b)`.

The proof first applies the general `model_integralPointMap` square
and then the original chart's evaluated integral-point-map theorem.
`mem_integralPoints_canonicalWeilModel_iff` states that a generic
point is integral precisely when its unitary parameters have this
form for some `a` and `b`. It uses the general subgroup membership
comparison and the original chart membership theorem.

For the lattice specialization, let
`ω : AddValuation L (WithTop ℝ)` satisfy
`IsRamifiedQuadraticValuation K L ω`: conjugation preserves the
valuation, nonzero elements of `K` have integral values, and some
element of `L` has value `1/2`. Assume `IsValuationIntegers O K ω`,
meaning that the image of `O` in `K` consists exactly of the
elements with nonnegative valuation.

In `SU3Root.IsRamifiedQuadraticValuation`,
`mem_integralPoints_canonicalWeilLatticeModel_iff` identifies the
integral points of the actual canonical restricted model at any
real depths `r` and `s` with `hω.filtrationProduct r s` under
`canonicalWeilRationalPointsEquiv`. The latter is the subgroup join
of the original unitary filtration at `r + μ/2` and its central
filtration at `s + μ`, where `μ = mu K L ω`. The existing central
normality theorem identifies this join with the product subgroup.
No ordering or strictness hypothesis on the two real parameters is
used. The original lattice chart internally takes central depth
`min s (2*r)`; the imported lattice membership theorem already
accounts for this convention.

The proof applies `AffineWeilGeneric.model_mem_integralPoints` to
the original smooth `latticeModel` and then its published
`mem_integralPoints_latticeModel_iff`.
`integralPoints_canonicalWeilLatticeModel_map` and
`integralPoints_canonicalWeilLatticeModel_comap` state the resulting
equalities of actual subgroups. Surjectivity of the generic
parameter equivalence supplies the reverse inclusion for the map
equality.

This unit completes the integral-point comparison for these canonical
restricted unitary models. Identifying these parameters and depths
with an ambient relative root group and supplied apartment data,
constructing compatible isomorphisms to arbitrary supplied root
models, and proving the full root-depth kernel theorem remain
separate obligations.
