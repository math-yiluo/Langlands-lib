# Integral subgroups in the completed tensor comparison

`localIntegralProduct` proves `LocalIntegralProductStatement` for number
fields `K` and `L` with an algebra structure `L/K` and a finite place `v`
of `K`. The canonical completed tensor map sends the subring
`localIntegers K L v` of `K_v ⊗[K] L` onto the product of the completed
integer rings of `L` at the places above `v`.

The definition of `localIntegers` takes the ring closure of the two
images of `O_v` and `𝓞 L`. The proof identifies this subring with the
range of the map from `𝓞 L ⊗[𝓞 K] O_v` induced by
`integralTensorInclusion` followed by `integralTensorTransport`. The
two kinds of generators are images of tensors with one factor equal to
one. In the other direction, tensor induction uses the fact that each
pure tensor maps to the product of one generator of each kind. The
Library's `integralLocalTensorComparison` computes the image of that
range under `finiteTensorMap`.

The completed tensor map is injective by `completedTensorComparison`.
It therefore detects membership in `localIntegers` by the valuation
ring membership of every coordinate. The lemma
`mem_integralSubgroup_localIntegers_iff` applies this test to the
entries of the matrix and of its inverse. It identifies the integral
subgroup on the local matrix model with the condition of belonging to
the integral subgroup in every factor.

This is an internal comparison of existing Library constructions. It
supplies the integral subgroup identification used in the product-unit
argument of Henniart–Lemaire, I.3.2, printed pp. 25–26 (PDF pp. 33–34).
The result holds at every finite place. Normalized Haar measure transport
and the finite-place cyclic coordinate presentation are further inputs
to the unit concordance application.
