# Square-zero kernels and units congruent to one

This internal construction generalizes the additive/unit comparison in
F. Oort, *Sur le schéma de Picard*, Bulletin de la Société Mathématique de
France 90 (1962), §6, Lemma 3, printed pp.6–7 (PDF pp.7–8 of the retained scan).
The registered original is `oort-1962-sur-le-schema-de-picard`, retained at
`literature/F. Oort - Sur le schema de Picard (1962).pdf`. The general
ring-map and naturality formulation here is derived infrastructure for
Picard deformation arguments. It does not assume that a ring map is
surjective, split, or a map of algebras over a field.

For commutative rings and a ring map `f : R →+* S`, `SquareZeroKernel f`
means that every product of two elements of the actual ideal `RingHom.ker f`
is zero. `squareZeroKernel_iff_ker_sq_eq_bot` proves its equivalence to
`(RingHom.ker f) ^ 2 = ⊥`, using the universal property of ideal
multiplication and membership of a product in the product ideal.
`UnitKernel f` is the actual group kernel of the induced map
`Rˣ →* Sˣ`. `oneAddUnit` sends a kernel element `a` to the unit with value
`1 + a` and inverse `1 - a`. The two inverse identities follow by
expansion and the square-zero hypothesis.

`kernelEquiv` is the multiplicative equivalence from
`Multiplicative (RingHom.ker f)` to `UnitKernel f`; its inverse sends a unit to its
value minus one. The multiplication law is the identity
`(1 + a)(1 + b) = 1 + a + b`, whose quadratic term vanishes.
`kernelAddEquiv` expresses the same equivalence in additive notation.

For a commuting square of ring maps, `additiveKernelMap` and
`unitKernelMap` are the actual maps induced on these kernels.
`unitKernelMap_equiv` proves their compatibility with `kernelEquiv`
by preservation of addition and one.

For any category `C`, commutative-ring presheaves
`F G : Cᵒᵖ ⥤ CommRingCat`, and natural transformation `η : F ⟶ G`,
`additiveKernelPresheaf η` takes the actual additive kernel of
`(η.app U).hom` at each object. `unitKernelPresheaf η` takes its actual
unit kernel, written additively. Their restriction maps are the kernel
maps above; `restriction_square` supplies the commuting square directly
from naturality of `η`. Their functor laws follow from the functor laws
of `F`, checked on the underlying ring elements or unit values.

If every component of `η` has square-zero kernel, `kernelPresheafIso η h`
is an isomorphism between these presheaves of abelian groups. Its
components are `kernelAddEquiv`, bundled by Mathlib's
`AddEquiv.toAddCommGrpIso`. Its naturality is exactly
`unitKernelMap_equiv`, in additive notation. Taking `C` to be the category
of opens gives the restriction-compatible presheaf comparison used in
Oort's Lemma 3. No topology or sheaf condition is imposed or asserted by
this generic presheaf construction.

This construction does not assert a Picard deformation classification,
surjectivity of a unit map, a comparison of cohomology theories, or
representability of any Picard functor.
