# Compact compression on images of actual rational inertia blocks

Worker 1751. This internal specialization of the generator-compression bridge
uses the actual rational inertia block and the actual compact induction from
the common norm kernel. It does not replace either object by an abstract
representation with similar properties.

`RationalInertiaImageStablePower G π T K hK g b` asserts stability of the
`b`-th compact-compression power on the image under `T` of every object of the
inertia block of `rationalInertiaBaseLift G π`. The base representation may have
an arbitrary carrier universe. The lifted block and its actual norm-kernel
compact induction have carrier universe `max uF uV`; their Hom-sized coproducts
have indices in that same universe. The output group and carrier universes are
independent.

`rationalInertiaImageStablePower_of_normKernel` assumes the exact existing
`IsRationalNormKernelSmallProgenerator` predicate. Its membership witness makes
the actual compact induction a block object. Its faithful Hom condition and
coproduct existence give the published two-coproduct generator presentations.
The actual block inclusion preserves finite colimits and the required
coproducts, by the published constituent and concrete-sum results. Composing it
with the supplied additive functor `T` therefore meets the hypotheses of
`functorCompressionStablePower_of_generator`. That theorem transfers stability
on the generator image to every block object with precisely the same exponent.

`rationalInertiaImageStationary_of_normKernel` takes one positive stable power
on the generator image and applies this transfer at its exponent. The
stable-power criterion then supplies both stationary power chains and their
complementarity for every image object from that common positive threshold.
The threshold precedes the quantified block object.

Right exactness, coproduct preservation, the generator predicate and generator
image stability remain explicit hypotheses. No representation admissibility,
finite dimension, finite type or finite length is imposed. These results do
not prove the norm-kernel generator predicate, generator image stability,
whole-category inertia decomposition, or the dynamic-parabolic uniform
stabilization endpoint.
