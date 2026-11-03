# Subgroup factorization from an all-test fixed coset

Worker 1293.

This internal construction extracts a genuine subgroup-scheme factorization
from an all-test fixed-coset equation. It works over any base scheme and
does not assume Borel, parabolic, smoothness or properness properties.

The data are actual group-scheme maps `i : H → G`, `j : K → G`, a supplied
relative scheme map `q : G → Q`, and a point `g` of G over the base.
The exact right-coset fiber condition says, for every scheme test T, that
`q(x) = q(y)` if and only if `x⁻¹ y` lies in the all-test range of j.
The fixed-coset hypothesis is the explicit equation
`q(i(h) g_T) = q(g_T)` for every T and every h in H(T).

`range_conjugate_le_of_fixed_coset` applies the fiber condition to
`x = g_T` and `y = i(h) g_T`. It obtains
`g_T⁻¹ i(h) g_T ∈ range(j)(T)`. The published formula for the actual
`innerIso` identifies this element with the image under
`i ≫ (G.innerIso g⁻¹).hom`, giving inclusion of represented subgroup
functors on all tests.

When the underlying maps of i and j are monomorphisms,
`factorOfFixedCoset` uses the published `SubgroupFunctor.factorOfRangeLE`
construction to return an actual homomorphism H → K.
`factorOfFixedCoset_comp` proves that its composite with j is exactly the
conjugated embedding. The inverse on the conjugating point reflects
the use of left action on right cosets.

The provenance is internal group algebra and the existing inner-automorphism
and represented-subgroup APIs. The fixed-coset equation is an input; this
module constructs neither a quotient action nor a fixed point nor a rational
lift. Those remain separate geometric obligations.
