# Finite residue coefficients and the actual elementary ideal sheaf

This internal construction works in every common universe `u`. Let `k` be a
commutative ring, `K` a field over `k`, `f : X → Spec k` an actual scheme
morphism, and `q : A → B` an elementary surjection of augmented Artinian
tests. Write `J = Kernel q`, with its canonical descended `K`-module
structure, and `i : X_K → X_A` for the actual residue morphism.
For the final comparison assume `Flat f` and supply a basis
`b : Basis ι K J` with finite index type `ι`. No section of the augmentation
`A → K` is assumed. A finite empty index type is permitted, so the
construction includes the zero kernel. Properness is not required.

`productSectionsIso` first identifies sections of a categorical product of
actual module sheaves with the product of their sections. This general
construction uses preservation of products by module evaluation and
`ModuleCat.piIsoPi`. `productSectionsIso_apply` identifies its coordinates
with the actual sheaf projections, using the two product comparison
projection identities. Naturality of those projections proves
`productSectionsIso_res`.

`tensorCoordinates b S` is the coordinate equivalence

```
S ⊗[K] J ≃ₗ[S] (ι → S)
```

given by the scalar-extended basis `(b.baseChange S).equivFun`. For a pure
tensor its `j`-th coordinate is `b.repr x j • s`.
`tensorCoordinates_map` proves that these coordinates commute with any
`K`-algebra map `S → T`. Tensor induction reduces the assertion to
linearity of that map on pure tensors and additivity on sums.

`residueStructureModule` is the actual module `i_* O_(X_K)` on `X_A`,
and `residueProductModule f ι` is the categorical product of `ι` copies
of this module. On an open `U` of `X_A`, put
`R = Γ(X_A,U)` and `S = Γ(X_K,i⁻¹U)`. The `R`-action on `S` is induced
by the actual map `i.app U`, as specified by `residueSourceAlgebra`.
`residueProductSectionsEquiv` identifies the actual product sections
with `ι → S`, linearly over `R`, and
`residueProductSectionsEquiv_res` proves compatibility with the actual
restriction to inverse-image opens.

`residueTensorCoordinates` restricts the `S`-linear coordinate
equivalence to the `R`-action. Composing its inverse with the product
section equivalence gives `productTensorEquiv`, an `R`-linear equivalence
from product-sheaf sections to `S ⊗[K] J` on every open. The coordinate
identity and `tensorCoordinates_map` prove
`residueTensorCoordinates_res`; injectivity of coordinates then proves
`productTensorEquiv_res`.

When `f` is flat and `U` is affine, `affineProductIdealEquiv` composes
`productTensorEquiv` with
`ArtinianResidueKernel.affineKernelResidueEquiv`, obtaining

```
Γ(residueProductModule f ι,U) ≃ₗ[R] Γ(idealModule f q,U).
```

The right side is the actual structure-map kernel module for
`X_B → X_A`. The two component restriction identities prove
`affineProductIdealEquiv_res`. Applying the inverse linear equivalence
to this identity also proves compatibility of the inverse maps.

`productToIdeal` and `idealToProduct` glue these compatible linear maps
and their inverses along the affine basis using `BasisHomGluing.hom`.
Their affine section formulas are `productToIdeal_app` and
`idealToProduct_app`. The two inverse identities hold on affine opens
by the corresponding identities of the linear equivalences;
`hom_ext_of_basis` proves them as identities of sheaf morphisms.
The result is the actual module-sheaf isomorphism

```
residueProductIdealIso f q b :
  residueProductModule f ι ≅ idealModule f q.
```

The provenance is internal: scalar-extended basis coordinates and
categorical product evaluation are combined with the previously constructed
actual affine kernel comparison, then glued using the sheaf condition.
The chosen basis is retained explicitly. No Picard representability or
atlas assertion is used. A cohomology comparison, naturality under changes
of the coefficient kernel, a formal hull, effectivity, and the exact
smooth Picard atlas remain further obligations.
