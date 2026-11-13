# Residue-product coordinates for the actual elementary ideal sheaf

This internal construction works directly on a scheme over the source of
an elementary local Artinian surjection. Its namespace is
`Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology.OriginalResidueProduct`.
It supplies an actual module-sheaf isomorphism and an explicit formula on
every open. The construction retains the original scheme and its actual
base-change ideal.

For the final isomorphism, let `R` and `S` be commutative local Artinian
rings in a common arbitrary universe `u`, with an algebra structure
`Algebra R S`. Write `φ₀ = algebraMap R S`, assume it is surjective, and
assume

```text
maximalIdeal R * RingHom.ker φ₀ = ⊥.
```

These two assumptions are supplied as `Fact` instances. Let
`X : Over (Spec R)` have flat structure morphism. Put `K = ResidueField S`
and `J = RingHom.ker φ₀`. Choose a basis `b : Basis ι K J` with finite
index type `ι : Type u`, using the descended action described below.
Neither properness nor a section of the residue map is required.
The empty index type, and thus the zero kernel, is allowed. A bare ring
homomorphism can be treated by choosing its `toAlgebra`; this pair
itself gives the isomorphism for the selected algebra map.

Let `X_K` be the actual pullback of `X` by
`Spec (residue S ∘ φ₀)`, and let `i : X_K → X` be its first projection.
Let `I = ideal φ₀ X`, the unchanged structure-kernel module of
`X ×_(Spec R) Spec S → X`. The main definition is

```text
residueProductIdealIso X b :
  (∏ᶜ fun _ : ι => i_* O_(X_K)) ≅ I.
```

The product is categorical in module sheaves on `X`, and the
isomorphism is linear for the actual structure sheaf of `X`.
Its forward map is `productToIdeal`, and its inverse is `idealToProduct`.

## Actual section maps and the affine residue ring

The initial definitions `residueInclusion`, `residueStructure`,
`sourceSectionHom`, `residueSectionHom`, and the associated algebra
structures are made for a general ring homomorphism `φ : R →+* S`
with local target. They use the actual pullback projection, actual
structure morphisms, their section maps, and the canonical
`Scheme.ΓSpecIso`. Here `residueStructure φ X` is `i_* O_(X_K)`.
`sourceSectionHom X U` sends an element of `R` to its actual structure
section on `U`. The residue section algebra is induced by
`X_K → Spec K`, and its source-section scalar action is induced by
`i.app U`.

`sourceSectionHom_res` and `residueSectionHom_res` are the corresponding
restriction identities. `residueSectionRestriction` bundles the latter
restriction as a `K`-algebra homomorphism.

For an affine open `U` of `X`, `affineSections_isPushout` identifies the
actual square of section rings as the pushout of `R → K` and
`R → Γ(X,U)`. Its proof applies the affine pullback section theorem
to the actual Cartesian square and transports the two spectrum
section rings through `ΓSpecIso`.

In the algebra-map setting, put `T = Γ(X,U)` and
`V = Γ(X_K,i⁻¹U)`. `affineSectionsEquiv` is the induced equivalence

```text
K ⊗[R] T ≃ₐ[K] V.
```

It sends `c ⊗ r` to the image of `c` on `X_K` multiplied by
`i.app U r`. In particular, `1 ⊗ r` maps to `i.app U r`.
`affineSectionsEquiv_res` proves compatibility with restriction
between affine opens by tensor induction, the two structure-section
restriction laws, and naturality of `i`. `sectionRestriction` and
`fibreRestriction` are the algebra maps in this identity.
`affineSectionsEquiv_smul` also proves linearity for the actual
`T`-action, using multiplication by `1 ⊗ r`.

## The actual ideal and its residue coefficients

`kernelResidueModule` uses `ArtinianSurjectionTests.arrow` to view
`φ₀` as an augmented Artinian-test arrow with common residue field
`K`. It then applies `ElementaryKernel.residueModule`. The underlying
additive group and `R`-module remain the actual ideal `J`.
`ElementaryKernel.augmentation_smul` gives the scalar tower from
`R` through `K` to `J`. No coefficient-field embedding is chosen.

For an affine `U`, `sourceSectionHom_flat` deduces flatness of
`R → T` from flatness of the actual structure morphism. With this
flatness, `affineKernelEquiv` composes the existing
`ElementaryKernelTensor.coefficientTensorEquiv`,
`ElementaryKernelTensor.idealTensorEquiv`, and
`AffineBaseChangeKernel.affine_ker` to obtain

```text
(K ⊗[R] T) ⊗[K] J ≃ₗ[T] Γ(I,U).
```

`affineKernelEquiv_tmul` computes the value of `(c ⊗ r) ⊗ x`,
after inclusion into `T`, as
`sourceSectionHom X U (c • x).val * r`.
The specialization at `c = 1` is
`affineKernelEquiv_one_tmul`. Nested tensor induction and the
structure-section restriction identity prove
`affineKernelEquiv_res`.

`coefficientSectionsEquiv` tensors `affineSectionsEquiv` with the
identity on `J` and verifies `T`-linearity on pure tensors and sums.
It identifies the preceding tensor domain with `V ⊗[K] J` and
commutes with restriction by `coefficientSectionsEquiv_res`.
Composing its inverse with `affineKernelEquiv` defines

```text
affineKernelResidueEquiv X U hU :
  V ⊗[K] J ≃ₗ[T] Γ(I,U).
```

Its compatibility with the earlier comparison is
`affineKernelResidueEquiv_coefficientSectionsEquiv`.
`affineKernelResidueEquiv_one_tmul` says that
`i.app U r ⊗ x` maps, after ideal inclusion, to
`sourceSectionHom X U x.val * r`.
`affineKernelResidueEquiv_res` proves compatibility with the actual
ideal-module restrictions.

## Product coordinates and gluing

`residueProductModule X ι` is the product of the residue structure
module. The existing `ArtinianResidueSheaf.productSectionsIso`
identifies its sections on every open with tuples of actual residue
sections. This defines `residueProductSectionsEquiv`; its restriction
law is `residueProductSectionsEquiv_res`.

`residueTensorCoordinates` uses
`ArtinianResidueSheaf.tensorCoordinates`, the scalar-extended basis
coordinate equivalence, and restricts its scalars to `Γ(X,U)`.
Its inverse composed with the product section equivalence defines
`productTensorEquiv`. The coordinate identity and
`residueTensorCoordinates_res` prove `productTensorEquiv_res`.
These constructions are defined on arbitrary opens.

On affine opens, `affineProductIdealEquiv` composes
`productTensorEquiv` with `affineKernelResidueEquiv`.
`affineProductIdealEquiv_res` proves compatibility with restriction.
Applying the inverse equivalence gives
`affineProductIdealEquiv_symm_res`.

`productToIdeal` and `idealToProduct` glue these maps and their
inverses with `BasisHomGluing.hom` along the affine basis.
Their formulas on affine opens are `productToIdeal_app` and
`idealToProduct_app`. The two inverse identities hold on that
basis by the inverse identities of the linear equivalences.
`hom_ext_of_basis` then proves the identities of sheaf morphisms
used in `residueProductIdealIso`.

## Formula for lifted tuples on every open

The formula section additionally supplies `Fintype ι`.
`productTensorEquiv_eq_sum` expands the tensor coordinates as the
finite sum of the residue coordinates tensored with `b j`, by
`Basis.equivFun_symm_apply` for the extended basis.

For any open `U`, let `r j : Γ(X,U)` be a family and let `s` be a
section of `residueProductModule X ι` on `U`. Suppose each actual
product projection of `s` is `i.app U (r j)`. Then
`productToIdeal_app_lift` proves

```text
((productToIdeal X b).app U s).val
  = ∑ j, sourceSectionHom X U (b j).val * r j.
```

The affine version, `productToIdeal_app_lift_affine`, expands
`productTensorEquiv_eq_sum` and uses finite-sum induction with
`affineKernelResidueEquiv_one_tmul`. The general version restricts
the equality to each affine open inside `U`. Naturality of the
product projections and of `unitToPushforwardUnit i` preserves
the lift hypothesis. Naturality of the ideal inclusion and
`sourceSectionHom_res` identify the two restricted expressions.
`eq_of_basis` for the actual structure module concludes equality
on `U`.

## Provenance and scope

Worker 208 authored this pair. Its provenance is internal: it combines
the Library's actual affine base-change kernel calculation and
elementary-kernel tensor equivalences with actual affine section
pushouts, finite basis coordinates, and sheaf gluing. The product
coordinate and gluing portion specializes the published
`ArtinianResidueSheaf` construction directly to the original scheme;
its generic product and tensor-coordinate helpers are reused.

This pair supplies the original-scheme objectwise presentation and
the lifted-tuple formula needed for a subsequent naturality square.
It does not assert that square for arbitrary morphisms, a
cohomology comparison, reduced-coproduct injectivity, or Picard
lifting or representability.
