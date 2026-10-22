# Tensor stability of colimit isomorphisms for varying-ring module diagrams

This file proves the Library statement
`Langlands.Algebra.Modules.tensorColimitIsIsoStatement` (module
`Langlands.Algebra.Modules.TensorColimitStatement`) as the theorem

```lean
theorem Langlands.Algebra.Modules.tensorColimitIsIso (C : Type u) [SmallCategory C]
    [IsCofiltered C] (R : Cᵒᵖ ⥤ CommRingCat.{u}) : tensorColimitIsIsoStatement C R
```

## Statement proved

Let `C` be a small cofiltered category and `R : Cᵒᵖ ⥤ CommRingCat` a presheaf of commutative
rings. Let `L` send a presheaf of `R`-modules `M` to `colim M`, the colimit over `Cᵒᵖ` of the
underlying presheaf of abelian groups of `M`. If `L f` and `L g` are isomorphisms for
`f : M₁ ⟶ M₂` and `g : N₁ ⟶ N₂`, then `L (f ⊗ₘ g)` is an isomorphism. Here `f ⊗ₘ g` is the
sectionwise tensor morphism `M₁ ⊗ N₁ ⟶ M₂ ⊗ N₂`, where `(M ⊗ N)(U) = M(U) ⊗_{R(U)} N(U)`.

## Setting (namespace `Langlands.Algebra.Modules.TensorColimit`)

Since `Cᵒᵖ` is filtered, Mathlib's `ModuleColimit` makes `colim M` a module over the colimit
ring `colim R` (computed in `RingCat`). The file works with this structure through
abbreviations:

- `Col M`: the colimit `colim M` with its `colim R`-module structure (`ModuleColimit` for the
  colimit cocones `colimit.isColimit`);
- `ι M : M(U) →+ Col M`: the colimit insertion; `ι_map` says `ι M (M.map f m) = ι M m`;
- `mapCol f : Col M →ₗ Col M'`: the linear map induced by `f` (`ModuleColimit.map`), with
  `mapCol_ι : mapCol f (ι M m) = ι M' (f.app U m)`;
- `smul_ι`: the image of `r ∈ R(U)` in `colim R` acts on `ι M m` as `ι M (r • m)`.

The local instances `IsFiltered.isSifted` and
`FinallySmall.preservesColimitsOfShape_of_isFiltered` (as in Mathlib's `ColimitFunctor`) make
the forgetful functors preserve the relevant colimits. The section variable
`[InitiallySmall.{u} C]` required by `ModuleColimit` is supplied in the final theorem by
`initiallySmall_of_essentiallySmall`.

## Construction

1. **Maps out of a colimit.** `descCol M φ hφ : Col M →+ P` is the map induced by a family of
   additive maps `φ U : M(U) →+ P` compatible with restriction (`descCocone`, `colimit.desc`);
   `descCol_ι` computes it on `ι M m`.

2. **The pairing `tmulHom : Col M →+ Col N →+ Col (M ⊗ N)`.** The cocone `tmulCocone` on the
   product of the underlying type-valued presheaves of `M` and `N`, with point `Col (M ⊗ N)`,
   sends `(m, n)` at `U` to the class `ιT M N (m ⊗ₜ n)` (`ιT` is `ι (M ⊗ N)` typed on
   `M(U) ⊗_{R(U)} N(U)`). Since filtered colimits of types commute with finite products, the
   product of the two colimit cocones is a colimit (`IsColimit.tensor`), and its `desc` gives
   a map `tmulAux : Col M → Col N → Col (M ⊗ N)` with
   `tmulAux_ι : tmulAux (ι M m) (ι N n) = ιT M N (m ⊗ₜ n)`. Biadditivity
   (`tmulAux_add_left/right`) and balancedness
   (`tmulHom_smul : tmulHom (a • x) y = tmulHom x (a • y)` for `a ∈ colim R`) are checked on
   representatives coming from a common index, using Mathlib's joint surjectivity lemmas
   (`ιM_jointly_surjective₂/₃`, `jointly_surjective₃'`) and the corresponding identities
   `add_tmul`, `tmul_add`, `smul_tmul` in `M(U) ⊗_{R(U)} N(U)`.
   `mapCol_tmulHom` shows `mapCol (f ⊗ₘ g) (tmulHom x y) = tmulHom (mapCol f x) (mapCol g y)`.

3. **Universal property of `Col (M ⊗ N)`.** For a biadditive map
   `B : Col M →+ Col N →+ P` that is balanced over `colim R`, `liftCol B hB : Col (M ⊗ N) →+ P`
   is `descCol` applied to the sectionwise maps
   `liftColApp B hB U = TensorProduct.liftAddHom (m, n ↦ B (ι M m) (ι N n))`; balancedness over
   `R(U)` follows from `smul_ι` and `hB`, and compatibility with restriction from `ι_map`
   (checked on pure tensors via `tensor_addHom_ext`). `liftCol_ιT` gives
   `liftCol B hB (ιT M N (m ⊗ₜ n)) = B (ι M m) (ι N n)`. The extensionality lemma
   `col_tensor_ext` says that two additive maps out of `Col (M ⊗ N)` agreeing on all
   `ιT M N (m ⊗ₜ n)` are equal (every element is some `ι (M ⊗ N) z` by
   `ιM_jointly_surjective`, and `z` is handled by induction on tensors).

## Proof

`bijective_mapCol_tensorHom`: assume `mapCol f` and `mapCol g` are bijective, and let
`e₁ = LinearEquiv.ofBijective (mapCol f)`, `e₂ = LinearEquiv.ofBijective (mapCol g)`. These are
`colim R`-linear, so `(x, y) ↦ tmulHom (e₁⁻¹ x) (e₂⁻¹ y)` is balanced, and
`ψ := liftCol` of it is an additive map `Col (M₂ ⊗ N₂) → Col (M₁ ⊗ N₁)`. Both composites
`ψ ∘ mapCol (f ⊗ₘ g)` and `mapCol (f ⊗ₘ g) ∘ ψ` are the identity by `col_tensor_ext`: on
`ιT (m ⊗ₜ n)` they reduce, via `mapCol_ιT`, `liftCol_ιT`, `mapCol_ι`, `mapCol_tmulHom` and
`tmulHom_ι`, to `ιT (m ⊗ₜ n)`. Hence `mapCol (f ⊗ₘ g)` is bijective.

`tensorColimitIsIso`: after introducing `M₁ M₂ N₁ N₂ f g` and the hypotheses, the three `IsIso`
conditions in `AddCommGrpCat` are rewritten with `ConcreteCategory.isIso_iff_bijective`. The
underlying functions of `L.map f`, `L.map g`, `L.map (f ⊗ₘ g)` are definitionally those of
`mapCol f`, `mapCol g`, `mapCol (f ⊗ₘ g)`, so `bijective_mapCol_tensorHom` closes the goal.

The proof never forms a tensor product over the colimit ring (which is only available as a
`RingCat` object); it works directly with balanced biadditive maps.

## Provenance

The target statement is internal to this project. The argument is the standard fact that
filtered colimits commute with tensor products, specialised to the colimit of sectionwise
tensor products of modules over a varying ring; the Lean route above is self-contained and
uses only Mathlib (`Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor`,
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal`, `Mathlib.Algebra.Category.Ring.Colimits`).
