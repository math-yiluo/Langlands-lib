# Ampleness and actual line twists from an affine base

This internal module proves that an actual line twist from an affine base does
not affect ampleness. Let `f : X ⟶ S` be a scheme morphism with `S` affine and
`X` compact and quasi-separated. Let `L` and `M` be actual line bundles on `X`,
let `B` be an actual line bundle on `S`, and supply an actual module-sheaf
isomorphism

```text
M.obj ≅ tensorObj L.obj ((Scheme.Modules.pullback f).obj B.obj).
```

The theorem `isAmple_iff_of_affine_base_twist` proves `M.IsAmple ↔ L.IsAmple`.
There is no properness, noetherian or triviality assumption on `B`. The
isomorphism premise concerns the actual tensor product and actual pullback,
not an equality of abstract Picard classes.

The definition `affineBaseTwistLocalIso` works over any base scheme. Given a
trivialization of the actual pullback of `B` to an open `U` of the base, it
constructs an isomorphism from the actual pullback of `M` to `f ⁻¹ᵁ U` to the
actual pullback of `L` there. Actual pullback composition, the restriction
square of `f`, tensor compatibility, pullback of the unit and the tensor
right unitor give this local comparison.

For the ampleness equivalence, an affine base supplies, at each base point,
a principal open inside a chosen trivializing neighbourhood of `B`. The
inverse image is a principal open on `X`; its inclusion is affine, so an
ample bundle restricts to an ample bundle there. The local comparison
transports this ampleness to the other bundle. The existing ampleness
locality theorem over an affine base then gives global ampleness. Applying
the argument in both directions proves the equivalence.

`LineBundle.IsAmple.tensor_pullback_of_affine_base` specializes to the
packaged actual tensor product with the pulled-back base line. The
provenance is internal: the proof combines existing actual pullback and
tensor isomorphisms with principal-open restriction and affine-base
ampleness locality. No particular determinant comparison or geometric
positivity is asserted. A later determinant application must supply its
actual tensor comparison, including its base determinant factor.
