# Natural convolution equivalence for affine Hopf-spectrum points

For a commutative Hopf algebra `C` over a commutative ring `R`, the
published `specPoint` construction identifies algebra maps `C → A`
with actual points of `Spec C` on the affine test `Spec A`.
`specPointMulEquiv` bundles this bijection as a multiplicative
equivalence from the convolution monoid of algebra maps to the group
of scheme-valued points. The multiplication equation follows by
comparing the existing `specPoint_mul` equation with the defining
convolution formula.

`specPoint_precomp` and `specPointMulEquiv_naturality` express
naturality under every coefficient-algebra map. They follow from
composition of the algebra-spectrum functor.

This is an internal adapter for the published `HopfSpecPoints`
constructions. It asserts no geometric action-rigidity conclusion.
