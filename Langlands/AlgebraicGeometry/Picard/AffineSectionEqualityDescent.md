# Equality of affine presheaf sections descends

This internal unit derives eventual equality of sections from the published
scheme-morphism equality descent theorem. It applies the result to the actual
Picard Isom presheaf using the existing focused representability propositions.
It makes no new assertion from the literature.

The slice object `Over.mk (𝟙 (Spec R))` is the identity base.
`affineBaseProjection R A` is the structure arrow from the affine algebra test
`Spec A` to this base. `HasAffineSubalgebraEqualityDescent F` says that two
sections of `F` on the identity base which have equal restrictions to `Spec A`
already have equal restrictions to `Spec B`, for some finitely generated
`R`-subalgebra `B` of `A`. The subalgebra must contain any prescribed finite set
of coefficients. The statement retains the actual sections and restriction
maps.

The scheme-point helper uses the published equality descent theorem with source
the identity of `Spec R` and target the locally finite type representative.
The first projection of the source pullback is its second projection followed
by the algebra structure map. Thus equality after affine restriction supplies
the theorem's equality premise. Its conclusion is pulled back along the
canonical section of the identity-source pullback, giving equality of the
two slice points after restriction to the finite algebra stage.

For a naturally represented presheaf, the inverse representation carries the
two sections to scheme points. Naturality transports their equality over the
large algebra. After descending that equality, naturality and injectivity of
the representation give equality of the original restricted sections.
The scheme-point helper needs only local finite type of the representative.
The presheaf consequence uses the existing affine finite-presentation
representation predicate.

The two Picard applications concern a proper flat locally finitely presented
morphism, two actual line-bundle families on an affine test base `Spec R`, and
their actual relative Isom presheaf on the full slice. They keep the focused
Isom or Hom representability premise explicit; the second application uses the
published Hom-to-Isom implication.

All rings, schemes and algebra tests have arbitrary universe `u`. No
noetherian, flatness or finiteness restriction is imposed on the algebra `A`.
This unit detects equality for sections initially defined on the identity
base. It does not itself construct a filtered-colimit category comparison,
prove infinitesimal gluing, or produce a smooth chart.
