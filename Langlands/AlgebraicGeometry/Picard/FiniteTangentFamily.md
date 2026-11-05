# Actual finite simultaneous first-order Picard families

This internal construction takes a commutative ring `k`, a field `K` with
`Algebra k K`, an actual morphism `f : X ⟶ Spec k`, and an actual line
bundle `M` on the residue relative scheme `Spec K ×_k X`. All schemes,
rings and the finite index type `ι` retain their arbitrary common universe
`u`. No properness hypothesis is needed.

For every family `v : ι → ArtinianDualNumberComparison.Classes f M`,
`family f M v` is an actual object of
`ArtinianTestDeformations.Deformations f M (FiniteTangents.test k K ι)`.
Thus it consists of an actual line bundle on the relative scheme over
`K ⊕ K^ι`, together with a specified isomorphism of its residue pullback
with `M`. The theorem `family_axis` says that pulling it back along the
`i`-th coordinate arrow gives the prescribed pointed isomorphism class
`v i`. This conclusion includes empty finite index types. The construction
chooses representatives; it does not assert a canonical choice of bundles
or of isomorphisms realizing the class equalities.

`OrdinaryClasses`, `restrictHom`, `forgetClass` and `restrictClass` use
the existing isomorphism-class quotient and actual relative pullback
functors. Their compatibility lemmas follow from line-bundle pullback
composition and the relative-space functor laws. In
`exists_deformation_of_class`, an ordinary class whose reduction is `[M]`
is represented by a bundle. Equality of residue classes supplies an actual
bundle isomorphism, which supplies the specified residue identification.

For actual dual-number targets, `forgetClass_dual_injective` proves that
ordinary forgetting is injective on pointed classes. The implemented
argument uses the published `ArtinianDualNumberComparison.classEquiv` and
`DualNumberThickening.pointedClassEquiv`. The latter identifies pointed
classes with the ordinary-class fibre over `[M]`, using the constant lift
to lift residue automorphisms. The comparison of underlying bundles
identifies this forgetful map with pullback along the actual dual-number
space isomorphism. This injectivity is used only at dual-number targets.

The ordinary class `dualSplit` is the constant lift of `[M]`. A direction
is normalized by dividing its underlying class by `dualSplit`; its
reduction is consequently the identity class. `simultaneousClass` is
the constant lift over `K ⊕ K^ι`, multiplied by the finite product of
the normalized classes pulled back along the coordinate inclusions.
Its reduction is `[M]`. Restriction to coordinate `i` kills every factor
whose index differs from `i`, since the corresponding composite factors
through the residue and normalization has trivial reduction. The remaining
factor cancels the normalization, giving the underlying class of `v i`.
Choosing an actual pointed representative of `simultaneousClass`, and
using dual-number forgetful injectivity, proves `family_axis`.

This derivation uses the explicit square-zero coordinate identities in
`ArtinianFiniteTangents` and the published actual dual-number comparison,
without an external existence theorem or general infinitesimal gluing.
It constructs a finite simultaneous first-order family. Weighted-sum
formulas, a tangent basis, higher-order compatible families, a formal hull,
algebraization and the smooth Picard atlas require further arguments.
