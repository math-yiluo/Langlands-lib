# Actual residue-coordinate compatibility for an elementary kernel quotient

This internal construction works in every common universe `u`, for a
commutative ring `k`, a field `K` over `k`, an actual scheme morphism
`f : X → Spec k`, an elementary surjection `q : A → B` of augmented
Artinian tests, and any `K`-submodule `W` of the actual `Kernel q` with its
existing descended residue action. Write `Q = A/W`, `π : A → Q` and
`r : Q → B` for the actual elementary quotient constructions. The maps
`i_A : X_K → X_A`, `i_Q : X_K → X_Q` and `h : X_Q → X_A` are the actual
maps of the relative schemes. No section of `A → K`, properness, or
nonzero-kernel hypothesis is used.

`residue_factorization` proves `i_Q ≫ h = i_A` by functoriality and the
specified augmentation triangle. For every open `U` of `X_A`,
`residue_open_eq` consequently identifies the actual opens
`i_Q⁻¹(h⁻¹U)` and `i_A⁻¹U` of the same residue scheme `X_K`.
`quotientResidueSectionMap` is actual section restriction along the
inclusion between these equal opens, packaged as a `K`-algebra map using
`ArtinianResidueSections.residueSectionRestriction`. It is independent
of the affine equivalences used below. Its scalar formula is
`quotientResidueSectionMap_scalar`. The section formula
`quotientResidueSectionMap_app` is

```
restriction (i_A.app U s) = i_Q.app (h⁻¹U) (h.app U s).
```

The latter follows from the scheme factorization; a generic helper proves
it by equality elimination and the presheaf identity law.

For an affine open `U` with affine inverse image `h⁻¹U`,
`affineSectionsEquiv_quotient` proves that the actual residue restriction
commutes with `ArtinianResidueSections.affineSectionsEquiv` and the
algebraic `ArtinianKernelQuotientTensor.quotientFibreMap`. Tensor induction
reduces the proof to the formula for `c ⊗ s`, using preservation of
multiplication, the actual residue scalars and the section formula above.
The additive case uses additivity of all maps. This comparison requires
no flatness. The affineness of the inverse image is supplied explicitly;
it holds since the actual quotient map is a closed immersion.

`quotientResidueTensorMap` is the `K`-linear tensor map

```
Γ(X_K,i_A⁻¹U) ⊗[K] Kernel q
  → Γ(X_K,i_Q⁻¹(h⁻¹U)) ⊗[K] Kernel r.
```

Its factors are the actual residue restriction and the existing
`ElementaryKernelSubspaceQuotient.kernelLinearMap`, whose underlying map
is the actual quotient on kernel elements. The unchanged residue actions
are used on both kernels. `coefficientSectionsEquiv_quotient` proves that
this map commutes with the two `ArtinianResidueKernel.coefficientSectionsEquiv`
maps and the algebraic `quotientTensorMap`. Tensor induction reduces this
to `affineSectionsEquiv_quotient` on pure tensors.

Assuming `Flat f`, `affineKernelResidueEquiv_quotient` proves, for every
tensor `t`,

```
(idealMap f q W).app U (affineKernelResidueEquiv f q U hU t)
  = affineKernelResidueEquiv f r (h⁻¹U) hV
      (quotientResidueTensorMap f q W U t).
```

Here `idealMap` is the independently constructed actual structure-kernel
map. First `affine_value_quotient` takes underlying section values in the
existing affine tensor compatibility theorem, using `idealMap_app` to
identify its left side with actual restriction through `h`. A generic
equivalence-transfer lemma then combines this value identity with
`coefficientSectionsEquiv_quotient`, giving `residue_value_quotient`.
Finally `idealMap_app` and subtype extensionality recover equality in the
actual target ideal. Thus no scalar action or quotient map is defined
through the comparison being proved.

The provenance is internal: these results combine the actual augmentation
factorization, section restriction and the existing affine tensor and
residue-section comparisons. They supply affine quotient compatibility
in actual residue coordinates. Global coefficient-sheaf and cohomology
naturality, obstruction naturality, a formal hull, algebraization, and
the exact smooth Picard atlas remain further obligations.
