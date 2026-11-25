# Tensor product distributing over a restricted product: the canonical maps (stand-in for Mathlib)

Module `Langlands.Mathlib.DedekindDomain.FiniteAdeleRing.TensorRestrictedProduct`. In the root name
space `RestrictedProduct` it declares the canonical maps that move a tensor factor inside an algebraic
restricted product,

```
M ⊗[R] Πʳ i, [N i, L i]_[ℱ]  →  Πʳ i, [M ⊗[R] N i, (image of M ⊗[R] L i)]_[ℱ],
m ⊗ x  ↦  (i ↦ m ⊗ x i),
```

namely `rangeLTensor`, `rangeLTensorLeft`, `lTensor`, `lTensorLeft`, `lTensor_tmul` and
`lTensorLeft_tmul`. It imports `Mathlib.RingTheory.TensorProduct.Basic` and the Mathlib stand-in
`Langlands.Mathlib.Topology.Algebra.RestrictedProduct.Basic` (for `mapAlongLinearMap`). It defines maps
only: no injectivity, surjectivity or bijectivity is proved here, and no flatness or finite presentation
is assumed. The index type, the filter and the coordinate submodules are arbitrary.

## Origin, stand-in status and licence

The file is taken from the Imperial College London FLT project
(github.com/ImperialCollegeLondon/FLT) at commit `0198058` (`019805815d7da565ed1e9f427b6fbd0cbc9d00d3`), file
`FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean`, lines 24-91. The project releases it under the Apache License 2.0; its licence is in
the Library at `licenses/ImperialCollegeLondon-FLT/LICENSE`, and the Lean file keeps the source's
copyright and author lines.

The file is a **stand-in for Mathlib**: the six declarations have the names that the Imperial project gives them, and
are expected in Mathlib under these names. The file is to be deleted when the Library's Mathlib has
these declarations; the modules that use them then import Mathlib's module instead.

Until 22 November 2026 these declarations were in `Langlands/LinearAlgebra/RestrictedProduct/`, ported
from the earlier Imperial commit `923d45174c500aa1d994ba973bac38ea39eacbf7`. The
declarations that the Imperial project declares under the same name were then moved
here, with the Imperial text of commit `0198058` wherever the declaration is the same one, so that this
file can be compared line by line with its source. The header of the Lean file gives the line ranges
taken and every difference.

The Imperial project keeps this file outside its directory `FLT/Mathlib/` of material sent to Mathlib.
Its declarations are in Mathlib's name space `RestrictedProduct`, and the Library keeps them as a stand-in
for Mathlib like the others (the declarations that the Imperial project declares under the
same name keep those names as Mathlib's future names).

Differences from the Imperial text: the module-system keywords are removed; the imports are Mathlib's
tensor products and the stand-in `Basic` instead of Imperial's `TensorPi`, `IsDirectLimit` and
`IsDirectLimitRestricted`, which these declarations do not need; the module docstring is the Library's;
only lines 24-91 are taken. The Imperial file goes on (lines 93-257) with
`coe_lTensorLeft_eq_lTensor`, `tmulEquivRangeLTensor`, `lTensorPrincipalEquiv`, `lTensor_bijective`,
`lTensorLeft_bijective` and the equivalences `lTensorEquiv`, `lTensorEquivLeft` with their `_tmul` lemmas.
The Library proves the bijectivity by its own argument
(`Langlands.LinearAlgebra.RestrictedProduct.tensorRestrictedProductComparison_proof`, in
`Langlands/LinearAlgebra/RestrictedProduct/TensorProof.lean`, which builds on this file), so it does not
take Imperial's direct-limit proof; the four equivalence declarations keep their Imperial names and
statements in `Langlands/LinearAlgebra/RestrictedProduct/TensorEquiv.lean`, where that theorem is
available.

## Image submodules

`rangeLTensor R M N L i` has arguments `R : Type u_1` and `M : Type u_2` with
`[CommRing R] [AddCommGroup M] [Module R M]`, an implicit `ι : Type u_3`,
`N : ι → Type u_4` with `[∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]`,
`L : ∀ i, Submodule R (N i)` and `i : ι`. It is the `R`-submodule

```
LinearMap.range (LinearMap.lTensor M (L i).subtype) ⊆ M ⊗[R] N i,
```

the image of `M ⊗[R] L i` under the map induced by the inclusion
`L i → N i`. The source docstring calls this "`M ⊗_R (L i)` as a submodule".
Without further hypotheses it is only the image. It is isomorphic to
`M ⊗[R] L i` when the induced map is injective, for instance when `M` is flat
over `R`. No such injectivity is asserted here.

`rangeLTensorLeft R M N L i` keeps the source's weaker hypotheses:
`[CommSemiring R] [CommSemiring M] [Algebra R M]`, coordinate semirings
`[∀ i, Semiring (N i)] [∀ i, Algebra R (N i)]`, and arbitrary `R`-submodules
`L i`. It is the range of Mathlib's heterobasic
`TensorProduct.AlgebraTensorModule.lTensor` applied to `(L i).subtype`, an
`M`-linear map `M ⊗[R] L i →ₗ[M] M ⊗[R] N i`. So it is the same image, now as
an `M`-submodule. Here `M` acts on `M ⊗[R] N i` through the left tensor
factor. It is declared `noncomputable`, as in the source.

## The canonical maps

### `lTensor`

```
lTensor R M N ℱ L :
  M ⊗[R] Πʳ i, [N i, L i]_[ℱ] →ₗ[R]
    Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ]
```

The hypotheses are those of `rangeLTensor`, together with an explicit
`ℱ : Filter ι`. The explicit arguments come in the source order `R M N ℱ L`.
The four universes `u_1` to `u_4` of `R`, `M`, `ι` and `N` are independent.

For `m : M`, the coordinate maps `TensorProduct.mk R M (N i) m : n ↦ m ⊗ n`
send `L i` into `rangeLTensor R M N L i`. This holds for every `i`, hence
`ℱ`-eventually: the image of `n ∈ L i` is the image of `m ⊗ ⟨n, hn⟩`. Thus
`mapAlongLinearMap` with `f = id` and `Filter.tendsto_id` gives an `R`-linear
map `x ↦ (i ↦ m ⊗ x i)`. It is additive and `R`-linear in `m`, which is
checked coordinatewise by `ext; simp`. `lTensor` is `TensorProduct.lift` of
this bilinear map.

### `lTensorLeft`

```
lTensorLeft R M N ℱ L :
  M ⊗[R] Πʳ i, [N i, L i]_[ℱ] →ₗ[M]
    Πʳ i, [M ⊗[R] N i, rangeLTensorLeft R M N L i]_[ℱ]
```

Here `R` and `M` are commutative rings with `[Algebra R M]`. The coordinates
`N i` are rings with `[∀ i, Algebra R (N i)]`, and the `L i` are arbitrary
`R`-submodules. The explicit arguments again come in the order `R M N ℱ L`,
with the universes of `R`, `M`, `ι` and `N` independent. The domain is an
`M`-module through the left tensor factor. The codomain is an `M`-module by
Mathlib's restricted-product `Module` instance, with each `rangeLTensorLeft`
an `M`-submodule.

The construction takes the `R`-linear map
`g = mapAlongLinearMap … id Filter.tendsto_id (fun i ↦ (n ↦ 1 ⊗ n)) _`, so
`g x i = 1 ⊗ x i`, and applies Mathlib's `LinearMap.liftBaseChange M`.
That function sends `m ⊗ x` to `m • g x`. The coordinate subobjects of the
codomain are `M`-submodules. To view the codomain as an `R`-module and `g` as
`R`-linear, the definition supplies
`SMulMemClass (Submodule M (M ⊗[R] N i)) R _` for each `i`, by
`SMulMemClass.ofIsScalarTower`. For `liftBaseChange` it proves
`IsScalarTower R M` on the codomain, coordinatewise. Both are local `have`
terms inside the body, proved from Mathlib's existing scalar actions. No
global instance and no extra hypothesis is added.

## Pure-tensor coordinate formulas

Both formulas are `simp` lemmas:

```
lTensor_tmul R M N ℱ L m f i :
  lTensor R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i)

lTensorLeft_tmul R M N L ℱ m f i :
  lTensorLeft R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i)
```

The hypotheses are those of the corresponding map. In `lTensorLeft_tmul`, `L`
comes before `ℱ` among the explicit arguments, as in the source.
`lTensor_tmul` holds by `rfl`. The proof of `lTensorLeft_tmul` unfolds
`lTensorLeft` and rewrites with `LinearMap.liftBaseChange_tmul`, the
coordinate formula `smul_apply` for restricted products, and
`mapAlongLinearMap_apply`. This turns the goal into `m • (1 ⊗ₜ f i) = m ⊗ₜ f i`,
which `simp` closes using `smul_tmul'` and `m • 1 = m`. That proof runs under
`set_option backward.isDefEq.respectTransparency.types false`, as in the
source. A private check without this option fails at the
`mapAlongLinearMap_apply` rewrite. The definition of `lTensor` is preceded, as in the source, by
`set_option backward.isDefEq.respectTransparency false in`; the Library's earlier port had dropped
that line, and it is back with the Imperial text.

## Checks

The module builds with Lean 4.35.0 and Mathlib `56a0058`. The types of the six declarations are the
same as before the move (compared declaration by declaration, binders and statement, on 22 November
2026).
