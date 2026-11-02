# Relative scheme points over product rings

This module constructs the relative map in Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (31 December 2011), formula (3.6.2), printed page 7,
and identifies its underlying map with the pinned Mathlib construction. The
registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source and the proof discussion on pages 7–8 were read for this construction.

For an arbitrary commutative ring `C`, a `C`-algebra `A`, and a scheme `X` over
`Spec C`, `ringTest C A` is `Spec A` with its actual structure morphism
`Spec.algebraMap C A`. `RingPoint C X A` is the morphism type from this object to
`X` in the slice category. Thus these are actual relative scheme points, including
points of nonaffine and nonseparated schemes.

`ringPointEquiv` identifies the slice morphisms with the subtype of scheme
morphisms `f : Spec A ⟶ X.left` satisfying
`f ≫ X.hom = Spec.algebraMap C A`. Its two inverses merely unpack and rebuild
the slice morphism. For `X = Spec B` with its given `C`-algebra structure,
`affineRingPointEquiv` composes this identification with Mathlib's
`AlgebraicGeometry.Spec.homEquivAlgHom`; the result is exactly `B →ₐ[C] A`.

Given an algebra homomorphism `f : A →ₐ[C] B`, `ringTestMap C f` is the
contravariant map `Spec B ⟶ Spec A` in the slice category. Its base equation
follows from `f.commutes`. The identity and composition lemmas are the
corresponding functor laws for `Spec`. `RingPoint.changeRing` is precomposition
with this morphism.

For an arbitrary family of commutative `C`-algebras `R i`, including an empty
family, `productPointMap C R X` sends a point over the actual product algebra
`∀ i, R i` to its restrictions along the spectra of the coordinate algebra
homomorphisms. `productPointMap_left` specifies the ring projection and its
contravariant direction. `productPointMap_underlying` proves that forgetting the
base equations gives exactly
`AlgebraicGeometry.pointsPi (fun i => CommRingCat.of (R i)) X.left`.
This identification is definitional; no alternate point presentation or assumed
comparison theorem is supplied as data. `productPointMap_natural` is associativity
of composition with a morphism over `Spec C`.

All rings and the index set are in an arbitrary common universe, matching
Mathlib's scheme and product-point interfaces. No topology, finite type,
separatedness, quasi-separatedness, quasi-compactness, or local-ring hypothesis
is needed for these constructions. The injectivity and surjectivity assertions
of (3.6.2), with their distinct source hypotheses, are separate statement and
proof units. In particular this construction does not yet assert the adelic
model-space comparison (3.6.1) or construct any adelic topology.
