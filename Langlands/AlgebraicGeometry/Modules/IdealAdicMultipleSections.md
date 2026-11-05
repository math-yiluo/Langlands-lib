# Quasi-coherence and affine sections of ideal multiples

This auxiliary module concerns the actual ideal-multiple sheaf constructed in
`IdealAdicQuotients`. It is internal support for the proof of the stable-image
statement; it does not establish the proper-cohomology estimate.

The morphism `scalarToMultiple` sends a section `m` to `a • m` in the
presheaf of multiples, for a base scalar `a` in the ideal.
The three main results are `inclusion_app_injective`,
`isQuasicoherent_multiple` and `mem_range_inclusion_app_iff`.
They retain arbitrary schemes and ideals; the last two require finite
generation of the ideal and quasi-coherence of the ambient module, and the
last also requires the chosen open to be affine.

For a finitely generated base ideal, choose finitely many generators and form
the finite direct sum of copies of the given module sheaf. Scalar multiplication
gives a surjective presheaf map onto the sectionwise span of ideal multiples.
The proof of surjectivity uses span induction, first for the ideal generators
and then for the module span. Sheafification gives an epimorphism from the finite
sum to the actual multiple, and its composition with the inclusion is the
original scalar-sum morphism.

Finite direct sums are quasi-coherent by the imported
`NoetherianApproximation.ModuleDescentCore.isQuasicoherent_biproduct`.
Images of quasi-coherent modules are also quasi-coherent,
so this epi-mono factorization proves quasi-coherence of the multiple. On an
affine open the epimorphism is surjective on sections. Its factorization through
the presheaf of multiples then proves that the range of the actual inclusion
is exactly the original sectionwise span. Independently of quasi-coherence,
the inclusion is injective on all opens because it is a monomorphism of sheaves.

These arguments derive the claims from the imported module sheafification,
finite biproduct, image and affine-section APIs. The scalar action and
ideal-multiple convention are exactly those of `IdealAdicQuotients`.
