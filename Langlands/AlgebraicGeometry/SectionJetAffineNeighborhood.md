# Finite-jet detection near a section on affine charts

`DetectsVanishingNearSectionAffine` says that an order `n` detects
vanishing near a section on every affine test scheme. If the extended
ideal is contained in the `(n + 1)`st power of the extended section
ideal, it vanishes on an open containing the changed section.
`exists_order_of_vanishing_near_section_affine` proves that such an order
exists for a smooth morphism of affine schemes and an ideal sheaf with
finitely generated global sections.

The construction uses the global section ring of the actual affine
pullback and its tensor-product comparison. The scalar-extension
augmentation is evaluation at the changed section. The ideal inclusion
gives vanishing in the tensor-product jet quotient. The affine algebra
theorem supplies an annihilator that evaluates to one at the section.
Inverting it yields the principal open. The conclusion is an inclusion
of the original ideal sheaf in the kernel of the composite from that open.

This internal lemma transfers the Library's section-jet algebra to affine
scheme charts. It supplies the neighborhood step used for equality of
morphisms after base change.
