# Actual ordinary first-order line-bundle classes and derived H1

This is an internal construction from the actual module-sheaf and cocycle
constructions imported by the Lean file. It applies to a scheme `X` over an
arbitrary field `k`, a fixed ordered affine cover `𝒰` of `X`, and the proved
pullback/tensor preservation property used by the line-bundle class group. The
comparison with derived cohomology additionally assumes that `X` is separated
over `Spec k`.

`DeformationClasses preservation f` is the subgroup of actual line-bundle
isomorphism classes on the actual dual-number thickening of `X` whose actual
zero-section pullbacks have trivial isomorphism class. Its multiplication is
the actual sheaf tensor product. No trivialization is retained as part of an
element of this subgroup.

`cocycleDeformationClass` takes an additive structure-sheaf cocycle on `𝒰` to
the line bundle glued with transitions `1 + ε zᵢⱼ`. The imported
`cocycleBundleReductionIso` proves that its zero-section pullback is trivial.
`cocycleDeformationHom` regards this construction as an additive group
homomorphism into `Additive DeformationClasses`; its addition law is the
imported actual tensor isomorphism. `cocycleDeformationHom_eq_iff` says that two
such classes are equal precisely when their difference is an additive
coboundary. This uses the arbitrary-gauge isomorphism criterion from
`DualNumberCocycleBundles`.

The imported `CechResolution.allPairsH1Map` is the surjective map from additive
cocycles to actual first right-derived relative cohomology of `structureSheaf X`.
Its kernel consists precisely of coboundaries. The structure sheaf is
quasi-coherent by the imported `CechDegreeOne.isQuasicoherent_unit`; the Lean
file supplies this instance explicitly for the structure-sheaf alias.
`h1Map_ker_le_cocycleDeformationHom_ker` therefore permits descent to the
additive homomorphism `h1DeformationHom` from actual derived H¹.

Injectivity follows by choosing cocycle representatives of two H¹ classes.
Equality of their bundle classes makes the difference a coboundary, so their
derived classes agree. For surjectivity, choose an actual line bundle
representing a deformation class. Triviality of its reduced isomorphism class
gives an actual reduction isomorphism. The imported
`exists_cocycle_presentation` constructs normalized frames on the prescribed
affine cover and an isomorphism to the bundle of an additive cocycle.

`deformationH1AddEquiv` is the inverse of this bijective additive homomorphism:
it identifies actual first-order ordinary line-bundle deformation classes with
actual derived structure-sheaf H¹. The terminal formula
`deformationH1AddEquiv_cocycleDeformationClass` identifies the image of each
normalized cocycle bundle with its actual derived cocycle class.

This unit proves an additive equivalence. It does not yet identify rigidified
classes or the parameter's tangent module, and it does not assert compatibility
with arbitrary field scalars. Those comparisons are separate prerequisites of
the final tangent-to-H¹ theorem. No external source-specific assertion is
introduced here.
