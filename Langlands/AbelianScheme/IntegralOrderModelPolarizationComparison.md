# Dual-valued maps on the actual integral order model

This internal application uses the existing `IntegralOrderModel`, its
`rationalAlgebraIso`, and the published integral dual-pullback construction.
It introduces no new geometric existence hypothesis.

For the original rational algebra action `α` and a full integer order, write
`β` for the full rational extension of the model's integral action. The model
supplies actual maps `f : A ⟶ B` and `g : B ⟶ A` with both composites equal
to a nonzero integer `N` times the identity. The existing rational comparison
has forward map `f` and inverse `N⁻¹ • g`.

`rationalExtension_inv_intertwines` multiplies the inverse comparison's
equivariance equation by `N` and cancels its nonzero rational denominator.
Thus the actual reverse map's rationalization intertwines all of `β` and
`α`. `rationalExtension_injective_iff` applies the full-action injectivity
invariance under `rationalAlgebraIso`; it concerns the entire rational
algebra, rather than only the integer order.

`dualPullbackHom` uses the existing `integralDualPullbackHom` to construct
`lamB = g ≫ lamA ≫ gᵛ`. `dualPullback_multiple` specializes the generic
inverse-multiple calculation to show that the rational pullback along `f`
is exactly `N² • lamA`, in the existing `IsRationalDualPullbackMultiple`
predicate. `dualPullback_multiple_pos` proves that this rational scalar is
positive using `N ≠ 0`.

`dualPullback_involutionCompatible` first identifies the rationalization
of the same integral composite with the published rational dual pullback.
It then applies involution compatibility under pullback along the reverse
map, using the whole-action equivariance proved above.

All actual dual representability, geometry, inverse-evaluation and
tensor/Picard coherence data are explicit. These conclusions are algebraic
comparisons. They do not assert that `lamB` is geometrically a polarization,
nor prove relative dimension, level structures or representability.
