# The actual stabilized quotient parabolic jet kernel

Authors: Worker 593, with Worker 796's quotient positivity and faithful-base-change inputs.

This internal derived comparison proves
`ParabolicSubgroupModuli.hasStabilizedJetKernelComparison`: for an affine group
scheme over `Spec R`, a reductive structure, an actual relative parabolic
inclusion, a supplied homogeneous quotient `Q`, and retained
`ProperQuotientJetData D`, the kernel of the actual stabilized jet tensor map
on every affine open of `Q` equals the submodule classified by the retained
Grassmannian embedding. It proves `HasStabilizedJetKernelComparison hG i hi Q D`
without an additional kernel, properness, positive-order or rank hypothesis.
The surrounding positivity result uses properness and positive order separately.

`quotientLiftOpen` is the inverse image of an affine quotient open under the
actual quotient projection. The projection is affine because the ambient group
is affine and the homogeneous quotient is separated. `quotientLiftCoefficient`
is the actual section pullback, with its prescribed base-ring algebra structure;
`quotientLiftConjugator` is the universal group point, expressed as a section of
the base-changed original group.

The proof first identifies the Grassmannian affine point after this exact
coefficient extension with the orbit point of the universal lift.
`quotientAffinePoint_map_eq_orbitPoint` uses the affine chart compatibility,
`D.embeddingData.fac`, and the all-test naturality of the orbit morphism. Thus
the classification map is the retained embedding of the actual quotient.

`quotientLiftCoefficient_faithfullyFlat` uses smoothness and surjectivity of
the homogeneous quotient projection and the affine section-ring criterion.
`quotientTensor_eq_zero_iff_orbit` then compares actual quotient-family jet
vanishing with actual conjugate-family jet vanishing along that lift, using
`ParabolicJetLiftComparison`, and applies the original parabolic's exact
conjugate tensor kernel theorem in `QuotientJetConjugateKernel`.

Finally `stabilizedTensorMap_ker` and
`globalFamilyTensorMap_ambientGlobalGenerator` identify the genuine stabilized
sheaf's tensor kernel with the product of this actual first-factor kernel and
zero on the pulled-back finite projective complement. The purely algebraic
`productKernel_eq_classified` reflects that equality through the faithfully
flat coefficient map. The conclusion is the actual stabilized kernel equality
on every affine quotient open, not an isomorphic replacement quotient or an
assumed comparison. The finite-family determinant-dual ampleness theorem is
assembled in a separate proof module.

The constructions and proof are internal to the existing actual quotient, jet,
Grassmannian and faithfully flat descent interfaces. No new literature claim or
source translation is made here.
