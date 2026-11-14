# Finite-kernel homomorphisms from smooth connected affine field groups

This internal helper proves `isFinite_hom_of_finite_kernel`. Over any field,
a homomorphism from a smooth connected affine group into an affine group
locally of finite type is a finite morphism if its actual scheme kernel is
finite. No surjectivity of the original map is assumed.

The proof factors the map through its smooth connected schematic image using
`HomImage.exists_image`. The inclusion is a closed immersion, so
`range_kernelι_comp_mono` identifies the full kernel ranges of the original
map and the projection to its image. The represented subgroup comparison
identifies the actual kernel schemes. Finiteness therefore transfers to
the projection's kernel. The published fpqc finite-kernel theorem
`isFinite_of_finite_kernel` makes that projection finite. Its composite
with the closed immersion is finite.

This is an internal composition of the named Library results, used to
construct the joint adjoint and cocenter map in the proof of bounded
adjoint preimages inside the rational norm kernel.
