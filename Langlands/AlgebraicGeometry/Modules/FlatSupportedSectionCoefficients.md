# Support-preserving coefficients under flat scalar extension

This internal unit extends the published field argument in
`ScalarExtensionKernels` and `SupportedSectionCoefficients` to a flat
homomorphism of commutative rings. The construction `FlatBaseChange.scalarKernelImage`
is the image of the scalar extension of the actual kernel inclusion.

Flatness identifies this image with the kernel of the extended map. Tensor
induction shows that a nonzero linear observation on this kernel is nonzero
on the extension of some actual downstairs kernel vector: otherwise it vanishes
on every pure tensor and hence on the whole tensor product. No faithful
flatness assumption is required for this coefficient argument.

For a commuting square of schemes, a specified line bundle, and canonical
scalar sections maps which are isomorphisms both on the scheme and on a
restricted coefficient module, `DerivedSections.FlatBaseChange.exists_vanishing_coefficient_generating`
extracts a downstairs section from an upstairs section in the restriction
kernel which generates at a chosen point. The downstairs section vanishes
after restriction and generates at the image point. The proof uses the
published commutation of scalar sections maps with restriction, the kernel
coefficient lemma, and the residue-field criterion for a line-bundle section
to generate at a point. The hypotheses include flatness of the base ring map
and the two canonical sections isomorphisms; this unit does not assert those
isomorphisms for arbitrary schemes or prove ampleness descent.

The provenance is internal: these constructions and proofs generalize the
existing field versions using flatness in exactly the tensor-exactness step.
