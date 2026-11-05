# Actual residue-fibre coefficients of elementary Picard kernels

This internal construction works in every common universe `u`, for a
commutative ring `k`, a field `K` over `k`, an actual scheme morphism
`f : X → Spec k`, and an elementary surjection `q : A → B` of augmented
Artinian tests. Write `J = Kernel q` for the unchanged actual ideal with its
canonical descended `K`-module structure, `X_A` and `X_K` for the actual
relative schemes, and `i : X_K → X_A` for the specified residue map.
The augmentation `A → K` need not have a section. The kernel may have any
finite dimension, including zero.

For an affine open `U` of `X_A`, write `R = Γ(X_A,U)` and
`S = Γ(X_K,i⁻¹U)`. The `K`-algebra structure on `S` comes from the actual
relative projection, as in `ArtinianResidueSections`.
`residueSourceAlgebra` equips `S` with the `R`-algebra structure induced by
`i.app U`. The algebraic fibre `K ⊗[A] R` has the right-factor `R`-action.
`affineSectionsEquiv_smul` proves that the canonical residue-section
algebra equivalence preserves these `R`-actions: express multiplication
by `r` in the tensor ring as multiplication by `1 ⊗ r`, then use its
multiplication law and coefficient-one formula. No flatness is used here.

`coefficientSectionsEquiv` tensors the canonical section equivalence
with the identity of `J`, giving

```
(K ⊗[A] R) ⊗[K] J ≃ₗ[R] S ⊗[K] J.
```

Its additive equivalence is `TensorProduct.congr`. Its `R`-linearity is
proved by tensor induction using `affineSectionsEquiv_smul` on pure
tensors and additivity on sums. This construction requires no map
`K → R`. `coefficientSectionsEquiv_tmul` states the defining formula
`y ⊗ x ↦ affineSectionsEquiv(y) ⊗ x`.
`coefficientSectionsEquiv_res` proves compatibility with actual
restriction for every inclusion of affine opens `V ≤ U`. The left
restriction tensors the actual `K`-linear residue-section restriction
with the identity of `J`; the right restriction uses `fibreRestriction`.
Tensor induction reduces this identity to `affineSectionsEquiv_res`.

Assuming `Flat f`, `affineKernelResidueEquiv` composes the inverse of
`coefficientSectionsEquiv` with `ArtinianPicardKernelTensor.affineKernelEquiv`.
The result is the actual source-section-linear equivalence

```
Γ(X_K,i⁻¹U) ⊗[K] J ≃ₗ[Γ(X_A,U)] Γ(idealModule f q,U).
```

Here `idealModule f q` is the actual structure-map kernel module for
`X_B → X_A`. `affineKernelResidueEquiv_coefficientSectionsEquiv` records
the composition formula. `affineKernelResidueEquiv_one_tmul` proves that
`i.app U r ⊗ x` maps, after taking the underlying ideal element, to
`testSectionHom f A U x.val * r`. This follows from the coefficient-one
formula for the two component equivalences.

`affineKernelResidueEquiv_res` proves compatibility with the actual
ideal-module restriction for every inclusion of affine opens `V ≤ U`.
Surjectivity of the coefficient-section equivalence reduces an arbitrary
tensor to the algebraic-fibre tensor case. The two component naturality
identities then prove the result. The residue opens in this equality are
the actual inverse images under `i`.

The provenance is internal: this unit composes the Cartesian affine
residue-section comparison with the flat ideal-tensor comparison, while
checking the original section-ring actions and restriction maps. It uses
no Picard representability or atlas assertion. It supplies the affine
coefficient comparison; a sheaf and cohomology comparison, formal hull,
effectivity and the exact smooth Picard atlas remain further obligations.
