# The exact centre-tangent kernel after field extension

Author: Worker 1487.

This internal deduction transports the exact full-centre differential kernel
through actual scheme base change. It uses the proved all-test identity
`center_baseChange` and the published comparison between the actual
dual-number kernels of a pullback group and its original group.

`SubgroupFunctor.mem_lie_baseChange_iff` identifies tangent membership in any
base-changed subgroup functor. Under the affine test-scheme comparison,
membership is preserved in both directions by restriction along an
isomorphism. `Lie.kernelBaseChangeLinearEquiv_target` identifies the
differentials under that comparison. Both lemmas apply over commutative rings,
with a compatible tower of coefficient algebras.

`ker_targetMapLinear_baseChange_eq_center_lie` then transports exact equality
of the differential kernel and the tangent submodule of the full centre.
Its proof rewrites the centre by its base-change identity, applies subgroup
tangent membership compatibility, and uses injectivity of the linear
comparison with the original target tangent space.

For a smooth connected affine source over any field,
`Lie.targetMap_baseChange_eq_one_iff_elementCentralizerLie_eq_top`
applies the semisimple centralizer criterion over any extension field.
Smoothness and affineness are preserved by pullback. The published geometric
connectedness theorem for smooth connected affine groups supplies
connectedness after field extension. No smoothness of the centre is used.

`GeometricCentralSemisimpleKernelStatement` expresses simultaneous quotient
existence in positive exponential characteristic. The theorem
`geometricCentralSemisimpleKernel` chooses a single smooth connected affine
central-isogeny quotient over the original field, retains its exact kernel
equality on all coefficient algebras, and proves the semisimple equivalence
after every field extension in the same universe. This includes the algebraic
closure and does not assume perfectness or infinitude of the original field.

This does not establish a decrease of torus weights, termination of iterated
quotients, lifting of target tori, or the parent no-torus theorem.

The local base-change instances have explicit names so their compiled
declarations remain distinct when the complete Library is imported together.
Their types, proofs, and local instance scope are unchanged.
