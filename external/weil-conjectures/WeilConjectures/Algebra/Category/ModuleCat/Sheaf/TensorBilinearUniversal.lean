/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Universal property of the sheaf tensor product

Source: literature/stacks-project/sites-modules.tex, Section 03EK, display after Tag 0GMW
(blueprint: lem-pc-sites-sheaf-tensor-bilinear-universal)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option autoImplicit false

attribute [local instance] monoidalCategory

/-- Existence part of the sheaf tensor universal property.
(blueprint: lem-pc-sites-sheaf-tensor-bilinear-universal)
The sectionwise tensor maps are assembled into a presheaf morphism and uniquely factored
through module sheafification; this is exactly the existence construction in the source proof. -/
private theorem tensor_bilinear_universal_exists {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (F G H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (β : ∀ U : Cᵒᵖ,
      F.val.obj U →ₗ[R.obj.obj U] G.val.obj U →ₗ[R.obj.obj U] H.val.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : F.val.obj U) (y : G.val.obj U),
      β V (F.val.map f x) (G.val.map f y) = H.val.map f (β U x y)) :
    ∃ φ : F ⊗ G ⟶ H, ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      φ.val.app U ((tensorObjIsoSheafification F G).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.app
            (F.val ⊗ G.val)).app U (x ⊗ₜ[R.obj.obj U] y))) = β U x y := by
  let q : F.val ⊗ G.val ⟶ H.val :=
    { app := fun U ↦ ModuleCat.ofHom (X := (F.val ⊗ G.val).obj U)
        (Y := H.val.obj U) (TensorProduct.lift (β U))
      naturality := by
        intro U V f
        ext t
        change TensorProduct.lift (β V) ((F.val ⊗ G.val).map f t) =
          H.val.map f (TensorProduct.lift (β U) t)
        induction t using TensorProduct.inductionOn with
        | tmul x y =>
          change β V (F.val.map f x) (G.val.map f y) = H.val.map f (β U x y)
          exact hβ f x y
        | add t s ht hs => simp only [map_add, ht, hs] }
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let a := (adj.homEquiv (F.val ⊗ G.val) H).symm q
  refine ⟨(tensorObjIsoSheafification F G).hom ≫ a, ?_⟩
  intro U x y
  have h := (adj.homEquiv (F.val ⊗ G.val) H).apply_symm_apply q
  rw [Adjunction.homEquiv_unit] at h
  have hh := congrArg (fun t ↦ (t.app U) (x ⊗ₜ[R.obj.obj U] y)) h
  change a.val.app U (((adj.unit.app (F.val ⊗ G.val)).app U)
    (x ⊗ₜ[R.obj.obj U] y)) = β U x y at hh
  change a.val.app U ((tensorObjIsoSheafification F G).hom.val.app U
    ((tensorObjIsoSheafification F G).inv.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) (x ⊗ₜ[R.obj.obj U] y)))) = _
  have hi := congrArg (fun t : (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).obj
        (F.val ⊗ G.val) ⟶ _ ↦ t.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) (x ⊗ₜ[R.obj.obj U] y)))
    (tensorObjIsoSheafification F G).inv_hom_id
  change (tensorObjIsoSheafification F G).hom.val.app U
    ((tensorObjIsoSheafification F G).inv.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) (x ⊗ₜ[R.obj.obj U] y))) = _ at hi
  rw [hi]
  exact hh
/-- Uniqueness part of the sheaf tensor universal property.
(blueprint: lem-pc-sites-sheaf-tensor-bilinear-universal)
A morphism out of the sheafified presheaf tensor is determined by its values on pure tensors,
by the generating property of the sectionwise module tensor and sheafification. -/
private theorem tensor_bilinear_universal_unique {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (F G H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (β : ∀ U : Cᵒᵖ,
      F.val.obj U →ₗ[R.obj.obj U] G.val.obj U →ₗ[R.obj.obj U] H.val.obj U)
    (φ ψ : F ⊗ G ⟶ H)
    (hφ : ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      φ.val.app U ((tensorObjIsoSheafification F G).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.app
            (F.val ⊗ G.val)).app U (x ⊗ₜ[R.obj.obj U] y))) = β U x y)
    (hψ : ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      ψ.val.app U ((tensorObjIsoSheafification F G).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.app
            (F.val ⊗ G.val)).app U (x ⊗ₜ[R.obj.obj U] y))) = β U x y) :
    φ = ψ := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  apply (cancel_epi (tensorObjIsoSheafification F G).inv).mp
  apply (adj.homEquiv (F.val ⊗ G.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  ext t
  change φ.val.app U ((tensorObjIsoSheafification F G).inv.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) t)) =
    ψ.val.app U ((tensorObjIsoSheafification F G).inv.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) t))
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact (hφ U x y).trans (hψ U x y).symm
  | add t s ht hs => simp only [map_add, ht, hs]

/-- Composition with the pure-tensor map `F × G → F ⊗_O G` is a bijection from
`Hom_O(F ⊗_O G, H)` to the set of morphisms of sheaves of sets `F × G → H` that are
`O(U)`-bilinear on sections over every `U`. A bilinear morphism is a family `β` of
`O(U)`-bilinear maps (curried linear maps) compatible with the restriction maps; the
pure-tensor map sends `(x, y)` over `U` to the image of `x ⊗ y` under the sheafification
unit of the presheaf tensor product, identified with `F ⊗ G` by
`tensorObjIsoSheafification`. The statement says that every such `β` is the composite of
exactly one morphism `F ⊗ G ⟶ H` with the pure-tensor map (naturality in `H` holds by
definition of the composite).
Source: literature/stacks-project/sites-modules.tex, Section 03EK, display after Tag 0GMW
(blueprint: lem-pc-sites-sheaf-tensor-bilinear-universal)
Proof: sectionwise, `O(U)`-bilinear maps `F(U) × G(U) → H(U)` correspond to `O(U)`-linear
maps `F(U) ⊗_{O(U)} G(U) → H(U)` (Tag 00CV), compatibly with restrictions, so restriction-
compatible bilinear families correspond to morphisms from the presheaf tensor product
[def-pur-presheaf-tensor-product] into `H`; since `H` is a sheaf, these factor uniquely
through the sheafification [def-weil-presheaf-modules-sheafification], which is `F ⊗_O G`
[def-pur-sheaf-tensor-product]. The resulting correspondence is composition with the
pure-tensor map and is natural in `H`.
-/
theorem tensor_bilinear_universal {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (F G H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (β : ∀ U : Cᵒᵖ,
      F.val.obj U →ₗ[R.obj.obj U] G.val.obj U →ₗ[R.obj.obj U] H.val.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : F.val.obj U) (y : G.val.obj U),
      β V (F.val.map f x) (G.val.map f y) = H.val.map f (β U x y)) :
    ∃! φ : F ⊗ G ⟶ H, ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      φ.val.app U ((tensorObjIsoSheafification F G).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.app
            (F.val ⊗ G.val)).app U (x ⊗ₜ[R.obj.obj U] y))) = β U x y := by
  obtain ⟨φ, hφ⟩ := tensor_bilinear_universal_exists R F G H β hβ
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  exact (tensor_bilinear_universal_unique R F G H β φ ψ hφ hψ).symm

end SheafOfModules
