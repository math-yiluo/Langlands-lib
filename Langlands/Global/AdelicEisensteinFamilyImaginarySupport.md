# Continuity and split-centre covariance on the imaginary support

`EisensteinFamilyImaginarySupportStatement` concerns a continued finite
Eisenstein family on a set of imaginary parameters in a real linear chart.
The set lies inside the family's domain of holomorphy. The family agrees
with its defining series on nonempty open patches at arbitrarily deep
regularity thresholds. Given pointwise continuation and joint root
hyperplane clearing, the family is jointly continuous on the set of
imaginary parameters times the adelic group. It is invariant under the
rational subgroup, and translation by a positive point of a split central
torus acts by the parameter power of its lift to the parabolic.

`eisensteinFamily_regularOn_imaginarySupport` applies `eisensteinFamilyRegularity`
in a complex chart. The map from the real chart into that chart is real
linear, so joint continuity restricts to the imaginary set. Rational
invariance restricts to the same set. For the centre, the positive point
maps into the split component of the Levi and its half-modulus is one
because its image in the ambient group is central. The split-component law
of the inducing vectors therefore supplies the scalar one in
`eisensteinFamilyRegularity`.

Lapid (2011), §2, pp. 311–312 (volume PDF pp. 320–321), gives the
split-component law and the continuation of the defining series. The
specialization to imaginary support gives the transformation law used
when applying the central Fourier transform in §8, p. 328
(volume PDF p. 337).
