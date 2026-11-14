# Transport of rank-one coroot parameters to the actual centralizer

This internal module derives conditional coroot calculations from supplied
coherent valued rank-one coordinates. It does not prove that these coordinates
exist. All fields have arbitrary universe `u`, and `F` is any nonarchimedean
local field, without a characteristic restriction.

For either coordinate type, the extension valuation used below is
`henselianSeparableAddValuation (MaximalUnramified.valuation F)
(MaximalUnramified.valuationSubring_isHenselian F) C.extension`. Thus all
depths retain the normalization of the original local field.

For `C : ValuedSL2RootCoordinates B hZ b`, `corootPoint` is the homomorphism
from `C.extension` units to the actual centralizer points obtained from
`WeilGm.rationalUnitsEquiv` and the supplied scheme-level coroot. The theorem
`commutator_factorization` maps the explicit SL2 opposite commutator
factorization through the single supplied `rho`.

For a nonzero character `b`, any apartment point, and two opposite-root
elements whose depths sum to a positive finite real `r`,
`exists_corootPoint_of_factorization` identifies the centralizer component
of any supplied opposite-root factorization with `corootPoint t`, where the
original-base-normalized henselian extension valuation of `t-1` is exactly
`r`. Opposite apartment translations cancel by
`KPApartmentData.opposite_value_sum_eq`; the common origin identifies the sum
with the scalar coordinate values. The SL2 pivot is nonzero by its valuation.
Finally `centralizerComponent_eq_of_root_factorizations` compares the
constructed factorization with the supplied one in the actual ambient group.

For `C : ValuedSU3RootCoordinates B hZ b`, the same construction defines
`corootPoint` from units of the quadratic extension. Here
`commutator_factorization` transports
`SU3Root.oppositeCommutator_factorization` through the supplied map on
the actual special unitary subgroup. The explicit outer factors have
parameters `q⁻¹ * oppositeProductLower p q` and
`oppositeProductUpper p q * p⁻¹`; the central parameter is the unit with
value `1 - p.first * bar(q.first) + p.second * q.second`.

At the ordinary unitary root, `exists_corootPoint_of_factorization`
identifies any supplied centralizer component with this coroot point and
proves that the value of the unit minus one is at least `r`. The common
origin and cancellation of opposite apartment translations identify the
sum of the two coordinate depths with `r`. A finite sum forces both
coordinate depths to be finite. Invariance of the normalized extension
valuation under the quadratic involution follows from
`SU3Root.henselianSeparableAddValuation_quadratic_bar`.
The explicit ordinary-depth estimates from `SU3RootOppositeBigCell`
then give the bound and nonvanishing of the pivot. Component uniqueness
again identifies the constructed point with the supplied `z`.

At the doubled unitary root,
`exists_corootPoint_of_double_factorization` uses the supplied
double-root equivalences to choose central parameters `p` and `q`.
Their first coordinates vanish. The double-root depth is the literal
value of the second coordinate, so cancellation of apartment
translations identifies
`omega(p.second) + omega(q.second)` with `r`, without a factor of two.
The identity
`oppositeProductPivot_sub_one_of_double` gives the exact value
`omega(t-1) = r`, which also proves that the pivot is nonzero. For
component uniqueness, the supplied outer factors at the doubled roots
are included in the ordinary opposite root groups by
`RelativeRoot.double_subgroup_le`. The constructed factorization can
therefore be compared at `b`; no assertion that its outer parameters
are central is needed.

This is derived transport algebra over the named Library interfaces. It does
not assert the coordinate existence target or an all-geometric-character
bound, and it is not the final `KPLocalCorootComponentStatement` proof.
