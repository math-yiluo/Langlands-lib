# Tangent maps from actual scheme stalks

This internal adapter uses the actual structure sheaf stalk at a rational point
of an arbitrary scheme over a field. All schemes, the field, and their stalks
lie in an arbitrary common universe. No finiteness or algebraic-closure
hypothesis is imposed.

For a structural morphism `p : X ⟶ Spec K` and a scheme point `z`,
`stalkAlgebraOver p z` equips `𝒪(X,z)` with a `K`-algebra structure. Its ring map
is `Spec.preimage (X.fromSpecStalk z ≫ p)`. Fully faithful `Spec` then identifies
the spectrum of this algebra map with the displayed structural composite.

If `x : Spec K ⟶ X` is a rational point, `rationalStalkAugmentation p x hx`
is the augmentation from the actual stalk at the image of the closed point.
Its underlying ring homomorphism is Mathlib's `Scheme.stalkClosedPointTo x`.
The canonical factorization through `Spec 𝒪(X,z)` reconstructs `x`; rationality
makes that factorization a map over `K`, so `Spec.homEquivAlgHom` gives an
actual `K`-algebra homomorphism.

`rationalStalkTangentMap` sends a dual-number algebra map on this stalk with
the prescribed augmentation to its spectrum followed by
`X.fromSpecStalk z`. The affine tangent equations and the two canonical
factorizations give precisely `Picard.IsTangentVectorAt p x`.

The map is injective because `X.fromSpecStalk z` is a preimmersion and hence
a monomorphism, and `Spec` is faithful. The same cancellation shows that the
resulting scheme tangent is constant exactly when the stalk algebra map is
the constant inclusion composed with `rationalStalkAugmentation`.

These constructions follow directly from Mathlib's stalk and spectrum APIs
and the project's tangent definitions; no external theorem is transcribed.
The module provides the direction needed to turn stalk algebra constructions
into tangent vectors. It does not claim surjectivity onto all tangent vectors
or a closed-immersion criterion.
