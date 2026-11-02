# Locality of total generic trivializing neighbourhoods

Let `R` be an arbitrary valuation domain, `K` any supplied fraction
field, and `p : X ⟶ Spec R` any smooth scheme morphism. For every actual
Library line bundle `D` on the actual fibre product
`X ×[Spec R] Spec K`, and every point `x` of `X`,
`smoothGenericTrivializingNeighbourhood` chooses an actual total open
neighbourhood `U` of `x` and an actual isomorphism from the restriction
of `D.obj` to `q⁻¹(U)` to the structure sheaf of that open. Here `q` is
the canonical first projection from that actual fibre product.
The universe is arbitrary, and there are no Noetherian, valuation-rank,
discreteness, properness or connectedness assumptions. Fields are
included.

The first lemma is independent of the valuation hypotheses. Consider a
cartesian square with maps `q : Y ⟶ X`, `q' : V ⟶ U`,
`i : V ⟶ Y` and `j : U ⟶ X`, where `i` and `j` are open immersions.
Suppose the pullback of `D` along `i` has a trivializing total
neighbourhood `N` at `x` in `U`. Set `W = q'⁻¹(N)` and
`T = j(N)`. The cartesian image-preimage identity gives
`i(W) = q⁻¹(T)`. Thus the open immersions `W ⟶ Y` and
`q⁻¹(T) ⟶ Y` have equal range, giving an isomorphism of their sources.
Pullback composition and the restriction-to-pullback comparisons
identify the given trivialization with a trivialization of the
pullback of `D.obj` restricted to `q⁻¹(T)` along this isomorphism.
The imported isomorphism-transport lemma recovers an actual
trivialization on `q⁻¹(T)`. Together with `j(x) ∈ T`, this proves
`nonempty_genericTrivializingNeighbourhood_of_isPullback`.

For an open chart `j : U ⟶ X` and any base change, form the pullback of
`j` along the canonical first projection. Pasting its cartesian square
with the original base-change square identifies its source with the
actual base change of `j ≫ p`, preserving the first projection to `U`.
The generic-source isomorphism-transport lemma and the first locality
lemma therefore transfer neighbourhoods on the chart's actual base
change to the original base change. This proves
`nonempty_genericTrivializingNeighbourhood_of_baseChange_chart`.

For an actual smooth morphism `Spec A ⟶ Spec R`, the fully faithful
spectrum functor recovers its coefficient ring map `R ⟶ A`.
The scheme smoothness-to-ring smoothness equivalence makes `A` smooth
with exactly that coefficient algebra. Rewriting the morphism by its
recovered spectrum map applies the imported affine neighbourhood
theorem to the actual fibre product. This proves
`hasGenericTrivializingNeighbourhoods_specSource`.

Finally choose an affine chart through each point of `X` and use its
canonical isomorphism with the spectrum of its global sections.
The composite of the inverse isomorphism and the chart inclusion is an
open immersion whose composite with `p` is smooth. The spectrum-source
result applies there, and base-change chart locality supplies the
required neighbourhood of the original point. This proves
`hasGenericTrivializingNeighbourhoods_of_smooth`; classical choice then
defines `smoothGenericTrivializingNeighbourhood`, including its actual
restriction-sheaf isomorphism.

The provenance is this internal derivation from
`SmoothValuationGenericNeighbourhood` and Mathlib's open-immersion,
cartesian-square, affine-cover and smoothness interfaces. This pair
asserts local generic trivializations on total open neighbourhoods.
Compatibility on intersections, a global total-space line bundle, and
the host two-axis extension statement remain to be proved.
