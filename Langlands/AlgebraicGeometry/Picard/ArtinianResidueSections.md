# Actual affine sections of the residue fibre

This internal construction works in every common universe `u`, for a
commutative ring `k`, a field `K` over `k`, an actual scheme morphism
`f : X → Spec k`, and an augmented Artinian test `A`. Write `X_A` and `X_K`
for the actual relative schemes, and `i : X_K → X_A` for the map induced by
the specified residue augmentation `A → K`. No section of this augmentation,
flatness, or properness is assumed.

`residueSectionHom` is the map `K → Γ(X_K, V)` induced by the actual relative
projection, composed with the canonical sections isomorphism for `Spec K`.
`residueSectionAlgebra` uses this map as the algebra structure.
`residueSectionHom_res` proves compatibility with restriction by the
`appLE_map` identity, and `residueSectionRestriction` packages the actual
restriction map as a `K`-algebra map.

For an affine open `U` of `X_A`, `affineSections_isPushout` proves that the
square with corners `A`, `K`, `Γ(X_A, U)`, and `Γ(X_K, i⁻¹U)` is a pushout
of commutative rings. The four maps are the original augmentation, the actual
source section map, the residue section map, and `i.app U`. The proof uses
`relativeProjection_isPullback`, the affine section-ring pushout theorem, and
the canonical spectrum sections isomorphisms at `A` and `K`.

`affineSectionsEquiv` turns this pushout into the canonical algebra equivalence

```
K ⊗[A] Γ(X_A, U) ≃ₐ[K] Γ(X_K, i⁻¹U).
```

The proof installs the two compatible `A`-actions on the target and applies
`Algebra.IsPushout.equiv` to the actual square. The pure-tensor formula
`affineSectionsEquiv_tmul` sends `c ⊗ r` to
`residueSectionHom f (i⁻¹U) c * i.app U r`.
`affineSectionsEquiv_one_tmul` gives the specialization `1 ⊗ r ↦ i.app U r`.

`affineSectionsEquiv_res` proves compatibility with actual restriction for
arbitrary nested affine opens `V ≤ U`. On the source, restriction is
`ArtinianPicardKernelTensor.fibreRestriction`, obtained by tensoring actual
section restriction with the identity of `K`. On the target, it is
`residueSectionRestriction` on the inverse-image opens. The proof is tensor
induction: on a pure tensor, use the multiplication formula, compatibility
of the residue action with restriction, and naturality of the actual scheme
map `i`; the additive step follows from additivity of the maps.

The construction is an internal consequence of the actual Cartesian geometry
and the affine section-ring pushout theorem. It supplies the residue-section
comparison needed by the elementary-kernel tensor construction. It does not
yet construct the resulting equivalence of sheaves or their cohomology,
a formal hull, or the smooth Picard atlas.
