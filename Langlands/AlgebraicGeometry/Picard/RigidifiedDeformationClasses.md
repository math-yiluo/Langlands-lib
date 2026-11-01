# Rigidified and ordinary actual first-order deformation classes

This is an internal construction from the published actual pullback functors,
rigidified compatible-isomorphism classes, and line-bundle isomorphism classes.
Its hypotheses are an arbitrary field `k`, a scheme `X` over `k`, a section of
its structure morphism, and the named pullback/tensor preservation proposition.
That last proposition has an existing proof in `Modules.PullbackTensorProof`.
No universal parameter, finite type assumption, or abelian-scheme structure is
needed for this comparison.

`LineBundle.classPullbackEquiv` gives the multiplicative equivalence on actual
line-bundle isomorphism classes induced by an actual scheme isomorphism.
Its inverse is pullback along the inverse isomorphism; the inverse identities
follow from the actual composition and identity isomorphisms for pullback.

`RigidifiedLineBundle.forgetClass` forgets rigidification in the relative family
over any test scheme. It is injective: the relative projection retracts the
relative section, and `nonempty_iso_of_forget_iso` uses this retraction to
correct an underlying line-bundle isomorphism into a compatible rigidified
isomorphism. When the test scheme has exactly one point, every line bundle
on that test scheme is trivial. Applying this to the section pullback of an
arbitrary relative line bundle supplies a rigidification, proving surjectivity.
`forgetClassEquiv` records the resulting equivalence. The file also proves
its actual pullback, trivial-class and tensor formulas directly on representatives.

The base relative fibre product over the identity of `Spec k` is canonically
isomorphic to `X`, by `DualNumberThickening.baseRelativeIso`. The two projections
prove that its composite with relative augmentation equals the actual
zero section followed by the inverse fibre-product symmetry. The actual
dual-number test scheme has exactly one point because the field spectrum has
one point and augmentation is surjective on underlying points.

`underlyingDualNumberClassEquiv` first forgets rigidification and then pulls
back along the inverse symmetry from the actual thickening to the relative
fibre product. It is an equivalence on all classes. Pullback composition and
the augmentation identity identify restriction of a rigidified class with
ordinary zero-section restriction after the canonical base identification.
The forgetting map at the base and pullback along this base isomorphism are
injective and preserve the trivial class. Therefore a rigidified class restricts
to the canonical trivial rigidified class exactly when the corresponding
ordinary class lies in `DualNumberThickening.DeformationClasses`, the kernel
of actual zero-section pullback.

`firstOrderDeformationEquiv` restricts the full equivalence using this exact
equivalence of conditions. It identifies the actual `FirstOrderClasses` with
the actual ordinary deformation subgroup, remembering classes without a chosen
reduction trivialization. Its underlying-class formula is definitional.
`underlyingDualNumberClassEquiv_tensor` says that the full equivalence sends
the actual rigidified tensor operation to the ordinary class product.

This focused construction supplies a type equivalence and the stated operation
formulas. The comparison of a universal parameter's sheaf tangent module with
these classes, and the final field-linear tangent/H1 comparison, are subsequent
obligations of the host task.
