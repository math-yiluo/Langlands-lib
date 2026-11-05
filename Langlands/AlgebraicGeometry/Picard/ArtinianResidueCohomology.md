# Actual elementary ideal cohomology with residue coefficients

This internal construction identifies the actual elementary ideal cohomology
with residue-fibre structure cohomology tensored with the elementary kernel.
It works in every common universe `u`, for a commutative ring `k`, a field
`K` with a `k`-algebra structure, a scheme morphism `f : X → Spec k`,
and an elementary arrow `q : A → B` of the actual augmented Artinian tests.
The kernel can have any finite dimension, including zero. The final
comparison assumes that `f` is flat and proper and retains a supplied
finite basis `b` of `Kernel q`. No section of the augmentation `A → K`
is chosen or assumed.

Write `X_A` and `X_K` for the actual relative spaces, `p_A` and `p_K`
for their structure morphisms, and `i : X_K → X_A` for the map induced
by the specified augmentation of `A`. Write `J` for the actual
structure-kernel module of `X_B → X_A`. The group `Cohomology f q n`
is the unchanged ideal-cohomology group from
`ArtinianPicardObstructionFinite`, used by the actual Picard obstruction.

## Finite products and tensor coordinates

`finiteProductCohomologyIso` constructs

```text
H^n_R(Y, ∏ᶜ_j M) ≅ ModuleCat.of R (j ↦ H^n_R(Y,M))
```

for any scheme morphism `Y → Spec R`, any module sheaf `M`, and any
finite index type. The right derived functor is additive, so it preserves
finite products. The construction composes its product comparison with
the concrete product isomorphism in `ModuleCat`. The lemma
`finiteProductCohomologyIso_apply` identifies each coordinate with
cohomology of the actual sheaf projection.

For any `K`-module `H`, `vectorTensorCoordinates b` is the linear
equivalence

```text
H ⊗[K] Kernel q ≃ₗ[K] (j ↦ H).
```

It composes Mathlib's tensor-to-finitely-supported coordinate equivalence
with the equivalence between finitely supported functions and functions
on a finite type. Its pure-tensor formula is
`(h ⊗ v)_j = b.repr v j • h`. Neither helper requires the index type
to be nonempty.

## The actual residue pushforward

`residueMap_isClosedImmersion` obtains the closed-immersion property
of `i` by base change from the actual residue immersion. Naturality of
the relative projection proves `residueMap_projection`:

```text
i ≫ p_A = p_K ≫ Spec.map A.augmentation.
```

`ResidueCohomology f n` is the actual relative cohomology
`H^n_K(X_K, O_X_K)`, with its existing `K`-module structure.
The definition `residueStructureCohomologyIso` composes the inverse
of affine-pushforward cohomology for the quasi-coherent unit module
with `relativeCohomologyBaseRingIso`. Its result is the `A`-linear
isomorphism

```text
H^n_A(X_A, i_* O_X_K) ≅
  restrictScalars A.augmentation (H^n_K(X_K, O_X_K)).
```

These constructions require neither flatness nor properness of `f`.
The scalar restriction is along the specified augmentation.

## Ideal cohomology and the descended field action

Assuming flatness, `idealCohomologyCoordinates` composes four actual
comparisons: `relativeEquiv`, cohomology of the inverse of
`residueProductIdealIso f q b`, finite-product cohomology, and
coordinatewise residue-pushforward cohomology. It is an `A`-linear
equivalence from `Cohomology f q n` to the product of the
augmentation-restricted residue-fibre cohomology modules.

With properness as well, `idealResidueCohomologyCoordinates` equips
the unchanged source group with exactly
`ArtinianPicardObstructionFinite.residueModule f q hq n`.
It retains the additive equivalence just constructed. To prove
`K`-linearity, lift a scalar through the surjective augmentation,
use `augmentation_smul` on the source, and apply `A`-linearity.
Thus the field action agrees with the previously defined descended
action, rather than being newly transported through the coordinates.

Finally, `idealCohomologyTensorEquiv` composes these field-linear
coordinates with the inverse tensor-coordinate equivalence:

```text
Cohomology f q n ≃ₗ[K]
  H^n_K(X_K, O_X_K) ⊗[K] Kernel q.
```

## Provenance and remaining work

This is an internal combination of the imported actual ideal-sheaf
presentation, affine-pushforward cohomology, restriction of scalars,
additive right-derived functors, and Mathlib's basis coordinates.
The proof route is described above and makes no additional literature
claim. The chosen kernel basis is explicit; basis independence and
naturality under changes or quotients of the elementary kernel are
not established here. The construction does not provide a formal
hull, effectivity, algebraization, or the exact smooth Picard atlas.
