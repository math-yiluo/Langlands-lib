# Unipotent radicals of actual subgroup preimages

This internal helper is derived from the published actual-kernel quotient,
ground-field radical existence, and unipotent extension results. Worker 74
implements it for the inverse-image construction in the nested-parabolic
extension task.

For an affine fppf homomorphism with smooth connected unipotent kernel, and
a represented radical in its target, the first theorem proves that the actual
group-scheme inverse image is a represented radical in the source. The source
is assumed smooth, connected and affine; the target is affine and locally of
finite type. The quotient is flat, scheme-surjective, locally of finite
presentation and quasi-compact.

The implementation obtains a source radical from the published existence
theorem and identifies its range with the full inverse image of the target
radical using `HasSmoothConnectedUnipotentKernel.radical_comap_eq`.
Smoothness, connectedness, normality and unipotence of the actual preimage
are checked through the pullback and the unipotent extension theorem.
Greatestness then follows from that all-test range identity.

The second theorem preserves the actual-kernel property under field extension
when both source and target are affine.
It uses the canonical kernel/base-change isomorphism, geometric connectedness
of a connected affine group of finite type, and the published preservation of
unipotence under field extension. All images and inverse images are subgroup
functors on arbitrary test schemes.

The third theorem proves the geometric version for the same supplied quotient
and a geometric radical in its target, using the
`LeviSubgroup.IsGeometricUnipotentRadical` predicate. It applies the first
theorem both over the original field and over its algebraic closure. Flatness,
surjectivity, finite presentation and quasi-compactness persist by pullback,
and the second theorem supplies the base-changed actual-kernel property.
The inverse image formed after base change and the base change of the original
inverse image have the same all-test range because both range and inverse image
commute with base change. Smoothness, connectedness and unipotence of the latter
follow from the ground-field radical; normality and greatestness transfer
through the range equality. No choice of a replacement inner Levi is involved.
