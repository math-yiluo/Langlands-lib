# Geometric coherence of scalar extension and inverse image

This internal construction extends `EtaleInverseImageScalars`. Let
`φ : R →+* S` be a homomorphism of commutative rings in `Type u`.
All schemes are `Scheme.{u}` and module carriers remain in universe `u`.
The geometric maps are arbitrary. There is no etale, affine, flatness or
finiteness hypothesis.

The input comparison is the previously constructed natural isomorphism

```text
sheafExtendScalars φ X ⋙ inverseImage f S
  ≅ inverseImage f R ⋙ sheafExtendScalars φ Z.
```

The present module proves its compatibility with the actual identity and
composition comparisons for geometric inverse image. It constructs a
two-step natural isomorphism and identifies the two ways to obtain it.

## The normalization by adjunction conjugation

For actual adjunctions `a : L ⊣ G`, `b : L' ⊣ G'`, and an actual right-adjoint
isomorphism `e : G ≅ G'`, the private helper `conjugate_scalarUniqueness`
proves that the conjugate of
`((a.ofNatIsoRight e).leftAdjointUniq b).hom` is `e.inv`.
It applies injectivity of the adjunction Hom correspondence, Mathlib's
conjugation counit equation, and the actual counit equation for
`leftAdjointUniq`. This is the same general argument used internally in
`EtaleInverseImageCoherence`.

`conjugate_inverseImageExtendScalarsIso` applies this computation to the
constructed composite scalar/geometric adjunctions. It identifies the
conjugate with the inverse of the actual
`directImageRestrictScalarsIso`. That comparison is the strict interchange
of sectionwise scalar restriction and evaluation at geometric base change.
It is constructed data, not a supplied desired comparison.

The other private helper identifies the conjugate of the inverse functor
associator. It follows by taking inverses of the natural-isomorphism
equality furnished by Mathlib's proved conjugation formula for the forward
associator.

## Identity and geometric composition

`inverseImageExtendScalarsIso_id` proves that scalar interchange along the
identity map, followed by scalar extension of `inverseImageId R X`,
equals `inverseImageId S X` applied after scalar extension. Its equality
of natural transformations includes the left and right functor unitors.

`inverseImageExtendScalarsIso_comp` proves the composition equation for any
`f : Z ⟶ X` and `g : V ⟶ Z`. Starting from
`(sheafExtendScalars φ X ⋙ inverseImage f S) ⋙ inverseImage g S`,
one route interchanges scalar extension with each inverse image and then
uses the geometric composition comparison with `R` coefficients.
The other route first composes the two geometric inverse images with `S`
coefficients and then interchanges with inverse image along `g ≫ f`.
The actual functor associators appear in the equality, including the
inverse associator needed to regroup the two `R`-coefficient inverse images.

Both proofs apply injectivity of adjunction conjugation. Mathlib's
composition and whiskering formulas reduce the diagrams to comparisons of
the actual right adjoints. The computed scalar conjugate and the
previously proved conjugates of geometric inverse-image identity and
composition reduce these to the same sectionwise direct-image/scalar
restriction maps. Their underlying presheaf maps agree definitionally.
Thus neither coherence equation is assumed.

## The actual two-step comparison

`inverseImageExtendScalarsTwoStepIso φ f g` constructs the first route as a
natural isomorphism with target
`inverseImage (g ≫ f) R ⋙ sheafExtendScalars φ V`.
`inverseImageExtendScalarsTwoStepIso_eq` proves that it equals the second
route as an actual natural isomorphism, by extensionality and the composition
equation above.

These are geometric identity and composition laws for the scalar-extension
comparison. Coherence in the ring homomorphism, agreement with the older
etale-restriction scalar comparison, inverse-image/scalar restriction,
and coefficient-change comparisons on cohomology remain separate.
No support, smooth-action or Harris specialization is asserted.
