# The cyclic valuation kernel of an actual maximal proper Levi

This derived unit applies the actual rational character decomposition in
`MaximalLeviCharacterDirection` to the valuation kernel defined in
`RationalUnramifiedRestrictionKernel`. It retains a connected reductive ambient
group over an arbitrary field, an actual maximal proper parabolic, its rational
Levi, and a split component.

For a group morphism `f : M → G` over a field, `HasOneIntegralDirection f`
asserts that a fixed character of `M` and the image of restriction from
`G` span every character of `M` after a positive integer multiple.
The theorem `exists_one_integral_direction` proves this for the actual
maximal Levi inclusion.

`exists_one_integral_direction` clears the rational coefficient denominator and
the tensor denominator of the ambient character in the rational decomposition.
The resulting equality of rationalized Levi characters is an
integral equality because restriction to the split component is injective and
the character lattice of that split torus injects into its rationalization.
The character direction is chosen once for all Levi characters; the positive
multiplier and ambient character may depend on the tested character.

`maximalLevi_rationalValuationKernel_isCyclic` then applies the existing
single-direction criterion to the kernel of the actual valuation-image map
induced by Levi inclusion. It holds for every nonarchimedean local field,
including positive characteristic. Cyclicity includes the trivial kernel.
