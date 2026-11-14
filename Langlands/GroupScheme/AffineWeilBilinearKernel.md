# Linear kernels in finite free restrictions of bilinear groups

Let `A` and `B` be commutative rings in an arbitrary common universe `u`,
with an `A`-algebra structure on `B` and a specified basis
`b : Basis (Fin n) A B`. For `z : B`, the entry `(j,l)` of
`AffineWeil.multiplicationMatrix b z` is the `j`th basis coefficient of
`z * b l`. The theorem `tensorCoordinateEquiv_mul` proves that, on every
`A`-algebra `T`, the tensor coordinate equivalence carries this matrix,
with coefficients mapped into `T`, to multiplication by `z` on `B ⊗[A] T`.
Its proof expands the tensor coordinate sum, exchanges two finite sums,
and uses the basis reconstruction formula and the balancing relation of
the tensor product. `tensorCoordinateEquiv_symm_mul` gives the inverse
coordinate formula.

The remaining constructions are in `AffineWeilBilinear`. Assume the finite
and projective module instances used to form the existing actual affine Weil
restriction. Let `I` and `J` be finite types in universe `u`, let
`c : I → I → B` and `d : J → J → B` be bilinear cocycles, and let
`M : I → J → B` and `t : B` satisfy
`BilinearCoordinate.IsCompatible c d M t`.
The original bilinear homomorphism sends `(a,z)` to
`((Σᵢ aᵢ Mᵢⱼ)ⱼ, t*z)`.
The homomorphism studied here is precisely its
`AffineWeil.map A B` between the actual affine restrictions.

`restrictionCoordinates` recovers tensor-valued bilinear coordinates from
points of the actual restriction on every scheme over `Spec A`.
It composes the original restriction's corepresented point equivalence
with the original bilinear group's affine point equivalence.
`restrictionBasisCoordinates` then takes all basis components, indexed by
`(I × Fin n) ⊕ Fin n`. These are set coordinates; they retain the bilinear
group law. Their naturality holds for every morphism of scheme tests, and
the identity point has zero coordinates.

The block matrix `linearMatrix` has vector entries given by
`multiplicationMatrix b (M i j)`, central entries given by
`multiplicationMatrix b t`, and zero off-diagonal blocks.
`basisCoordinateEquiv_linearMap` verifies its formula on tensor-valued
bilinear coordinates. `restrictionCoordinates_linearHom` uses the
corepresented map formulas twice to identify the original restricted map.
Combining these facts proves `restrictionBasisCoordinates_linearHom`:
this actual homomorphism has the asserted matrix formula on every scheme
test, with the matrix coefficients evaluated through the scheme's
structure map.

When `A = k` is a field, `linearKernel_properties` proves that the
scheme-theoretic kernel of this actual restricted homomorphism is smooth,
connected and unipotent over `k`. It applies
`PolynomialLinearKernel.properties` to the natural finite set coordinates
and the matrix formula just proved. The source is affine and locally of
finite type by the existing restriction construction; its smoothness,
connectedness and unipotence come from `AffineWeilBilinear.properties`.
The target is affine and hence separated. The kernel theorem constructs
a scheme retraction using an inner inverse of the matrix and obtains
unipotence from the closed-subgroup theorem. It does not require the
coordinate equivalences to preserve an additive law.

There is no reducedness, separability, perfectness or residue-characteristic
hypothesis. In particular, nilpotent coefficients in a finite algebra
over `k` are covered. Empty vector index types and rank zero are allowed.

This is a derived prerequisite for the restriction-of-scalars assembly in
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Proposition
C.5.1, printed pp.703–704 / PDF pp.734–735, and the special-fibre kernel
assertion in Lemma C.5.3, printed p.705 / PDF p.736. The source uses
restriction of the root building-block models; this general bilinear
matrix calculation is an internal derivation, rather than a literal
restatement of the book. The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

This unit does not identify an arbitrary supplied root-depth model or its
special fibre with these restrictions. Those comparisons remain necessary
for the full C.5.3 theorem. No host KP Proposition 8.4.15 kernel theorem is
used.
