/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Category.Grp.FilteredColimits

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-!
# Tensor-Hom adjunction on a ringed space

Source: Stacks Project, Modules, Lemma 01CN, the morphism correspondence
(blueprint: lem-weil-pbc-module-tensor-hom-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace

namespace SheafOfModules

set_option autoImplicit false

section Helpers

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡" =>
  ((sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat.{u})).obj R)

noncomputable local instance : MonoidalCategory (SheafOfModules.{u} 𝓡) := monoidalCategory R

private noncomputable def correspondence
    (A G F : SheafOfModules.{u} 𝓡) :
    (A ⟶ homObj (R := R) G F) ≃ (A ⊗ G ⟶ F) :=
  (((fullyFaithfulForget 𝓡).homEquiv
    (X := A) (Y := homObj (R := R) G F)).trans
    (PresheafOfModules.homObjEquiv (R := R.obj) G.val A.val F.val).symm).trans
    (((β_ G.val A.val).homFromEquiv.trans
      ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)).homEquiv
        (A.val ⊗ G.val) F).symm).trans
      (tensorObjIsoSheafification A G).symm.homFromEquiv)

private lemma correspondence_eval (A G F : SheafOfModules.{u} 𝓡)
    (φ : A ⟶ homObj (R := R) G F) (W : Opens X)
    (a : A.val.obj (op W)) (g : G.val.obj (op W)) :
    (correspondence A G F φ).val.app (op W)
      ((tensorObjIsoSheafification A G).inv.val.app (op W)
        (((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)).unit.app
          (A.val ⊗ G.val)).app (op W) (a ⊗ₜ[R.obj.obj (op W)] g))) =
      (φ.val.app (op W) a).app (op (Over.mk (𝟙 W))) g := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)
  let q : A.val ⊗ G.val ⟶ F.val :=
    (β_ G.val A.val).inv ≫ PresheafOfModules.tensorHomUncurry φ.val
  have h := (adj.homEquiv (A.val ⊗ G.val) F).apply_symm_apply q
  rw [Adjunction.homEquiv_unit] at h
  have hh := congrArg (fun t ↦ t.app (op W) (a ⊗ₜ[R.obj.obj (op W)] g)) h
  have hi := congrArg (fun t ↦ t.val.app (op W)
      ((adj.unit.app (A.val ⊗ G.val)).app (op W)
        (a ⊗ₜ[R.obj.obj (op W)] g)))
    (tensorObjIsoSheafification A G).inv_hom_id
  change (tensorObjIsoSheafification A G).hom.val.app (op W)
    ((tensorObjIsoSheafification A G).inv.val.app (op W)
      ((adj.unit.app (A.val ⊗ G.val)).app (op W)
        (a ⊗ₜ[R.obj.obj (op W)] g))) = _ at hi
  change ((adj.homEquiv (A.val ⊗ G.val) F).symm q).val.app (op W)
    ((tensorObjIsoSheafification A G).hom.val.app (op W)
      ((tensorObjIsoSheafification A G).inv.val.app (op W)
        ((adj.unit.app (A.val ⊗ G.val)).app (op W)
          (a ⊗ₜ[R.obj.obj (op W)] g)))) = _
  rw [hi]
  exact hh

private lemma pure_tensor_ext (A G F : SheafOfModules.{u} 𝓡)
    (ψ χ : A ⊗ G ⟶ F)
    (h : ∀ (W : Opens X) (a : A.val.obj (op W)) (g : G.val.obj (op W)),
      ψ.val.app (op W) ((tensorObjIsoSheafification A G).inv.val.app (op W)
        (((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)).unit.app
          (A.val ⊗ G.val)).app (op W) (a ⊗ₜ[R.obj.obj (op W)] g))) =
      χ.val.app (op W) ((tensorObjIsoSheafification A G).inv.val.app (op W)
        (((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)).unit.app
          (A.val ⊗ G.val)).app (op W) (a ⊗ₜ[R.obj.obj (op W)] g)))) : ψ = χ := by
  apply (cancel_epi (tensorObjIsoSheafification A G).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)).homEquiv
    (A.val ⊗ G.val) F).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a g
  exact h U.unop a g

noncomputable local instance homModuleLocal (M N : SheafOfModules.{u} 𝓡) :
    Module (RingCat.sectionsSubring (𝓡).obj) (M ⟶ N) :=
  homModule R.obj (𝓡).property M N

private lemma correspondence_add (A G F : SheafOfModules.{u} 𝓡)
    (φ χ : A ⟶ homObj (R := R) G F) :
    correspondence A G F (φ + χ) = correspondence A G F φ + correspondence A G F χ := by
  apply pure_tensor_ext
  intro W a g
  rw [correspondence_eval]
  change _ = (correspondence A G F φ).val.app (op W) _ +
    (correspondence A G F χ).val.app (op W) _
  rw [correspondence_eval, correspondence_eval]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma correspondence_smul (A G F : SheafOfModules.{u} 𝓡)
    (s : RingCat.sectionsSubring (𝓡).obj) (φ : A ⟶ homObj (R := R) G F) :
    correspondence A G F (s • φ) = s • correspondence A G F φ := by
  apply pure_tensor_ext
  intro W a g
  rw [correspondence_eval]
  change _ = s.val (op W) • (correspondence A G F φ).val.app (op W) _
  rw [correspondence_eval]
  change ((PresheafOfModules.sectionsSMul _ s).app (op W)
    (φ.val.app (op W) a)).app (op (Over.mk (𝟙 W))) g = _
  rw [PresheafOfModules.sectionsSMul_app_apply]
  rw [PresheafOfModules.smul_app]
  erw [ModuleCat.comp_apply, PresheafOfModules.sectionsSMul_app_apply,
    PresheafOfModules.overSections_coe_apply]
  simp

set_option backward.isDefEq.respectTransparency false in
private lemma correspondence_natural (A A' G F : SheafOfModules.{u} 𝓡)
    (α : A' ⟶ A) (φ : A ⟶ homObj (R := R) G F) :
    correspondence A' G F (α ≫ φ) = (α ⊗ₘ 𝟙 G) ≫ correspondence A G F φ := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)
  have hi : (tensorObjIsoSheafification A' G).inv ≫ (α ⊗ₘ 𝟙 G) =
      (PresheafOfModules.sheafification.{u} (𝟙 (𝓡).obj)).map (α.val ▷ G.val) ≫
        (tensorObjIsoSheafification A G).inv := by
    rw [tensorHom_id, Iso.inv_comp_eq, ← Category.assoc,
      ← whiskerRight_tensorObjIsoSheafification_hom (R := R) α G, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hn := adj.unit.naturality (α.val ▷ G.val)
  change (α.val ▷ G.val) ≫ adj.unit.app (A.val ⊗ G.val) =
    adj.unit.app (A'.val ⊗ G.val) ≫
      ((PresheafOfModules.sheafification.{u} (𝟙 (𝓡).obj)).map (α.val ▷ G.val)).val at hn
  have hp : adj.unit.app (A'.val ⊗ G.val) ≫
      (tensorObjIsoSheafification A' G).inv.val ≫ (α ⊗ₘ 𝟙 G).val =
      (α.val ▷ G.val) ≫ adj.unit.app (A.val ⊗ G.val) ≫
        (tensorObjIsoSheafification A G).inv.val := by
    have hv := congrArg SheafOfModules.Hom.val hi
    change (tensorObjIsoSheafification A' G).inv.val ≫ (α ⊗ₘ 𝟙 G).val = _ at hv
    change (tensorObjIsoSheafification A' G).inv.val ≫ (α ⊗ₘ 𝟙 G).val =
      ((PresheafOfModules.sheafification.{u} (𝟙 (𝓡).obj)).map
        (α.val ▷ G.val)).val ≫ (tensorObjIsoSheafification A G).inv.val at hv
    erw [hv, ← Category.assoc, ← hn, Category.assoc]
  apply pure_tensor_ext
  intro W a g
  rw [correspondence_eval]
  have hp' := congrArg (fun t ↦ t.app (op W) (a ⊗ₜ[R.obj.obj (op W)] g)) hp
  change _ = (correspondence A G F φ).val.app (op W)
    ((α ⊗ₘ 𝟙 G).val.app (op W) _)
  change (α ⊗ₘ 𝟙 G).val.app (op W)
    ((tensorObjIsoSheafification A' G).inv.val.app (op W)
      ((adj.unit.app (A'.val ⊗ G.val)).app (op W)
        (a ⊗ₜ[R.obj.obj (op W)] g))) =
    (tensorObjIsoSheafification A G).inv.val.app (op W)
      ((adj.unit.app (A.val ⊗ G.val)).app (op W)
        (α.val.app (op W) a ⊗ₜ[R.obj.obj (op W)] g)) at hp'
  rw [hp', correspondence_eval]
  rfl

end Helpers

/-- Tensor-Hom correspondence, linear over global sections, characterized on local pure
tensors and natural in the first factor. The tensor product `A ⊗ G` is the source's
`SheafOfModules.monoidalCategory R` [def-pur-sheaf-tensor-product]; `t_W` is the
sheafification unit followed by `SheafOfModules.tensorObjIsoSheafification`.
Source: Stacks Project, Modules, Lemma 01CN
(blueprint: lem-weil-pbc-module-tensor-hom-adjunction).

Proof: (1) On opens, internal Hom consists of module maps on the slice; restriction
restricts these maps, and scalars act sectionwise [def-pur-sheaf-hom].
(2) Apply Algebra 00DE [lem-weil-pbc-module-tensor-hom-currying] on every open to the
bilinear map `(a,g) ↦ (φ_W(a))_W(g)`, obtaining a linear map from the section tensor product.
(3) These maps commute with restrictions: check on pure tensors using naturality of `φ`
and of the local maps it gives. Pure tensors generate, so they define a presheaf morphism
[def-pur-sheaf-tensor-product, def-weil-presheaf-modules-sheafification].
(4) Conversely, a presheaf tensor morphism `ψ` gives at `a ∈ A(W)` the local map with
component on `W' ⊆ W` given by `g ↦ ψ_W'(a|_W' ⊗ g)`. Naturality of `ψ` makes this a local
module morphism; linearity and restriction compatibility give a map into internal Hom.
(5) The constructions are inverse by evaluation on local sections and generation by pure
 tensors [lem-weil-pbc-module-tensor-hom-currying, def-pur-sheaf-hom].
(6) The universal property of module sheafification transports the presheaf morphism to
 a unique sheaf morphism with the displayed evaluation formula
[def-weil-presheaf-modules-sheafification, def-pur-sheaf-tensor-product].
(7) Sectionwise evaluation commutes with addition and multiplication by a global section;
 uniqueness makes the correspondence linear [def-pur-sheaf-modules-hom-module].
(8) Precomposing by `α` gives the same evaluation formula as precomposing the tensor
 morphism by the sheafification of `α ⊗ id`; uniqueness gives naturality.
-/
theorem exists_tensorHom_linearEquiv (X : Type u) [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (G F : SheafOfModules.{u} ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)) :
    letI := monoidalCategory R
    letI : ∀ M N : SheafOfModules.{u}
        ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R),
        Module (RingCat.sectionsSubring
          ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R).obj) (M ⟶ N) :=
      homModule R.obj ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R).property
    ∃ e : ∀ A : SheafOfModules.{u}
        ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R),
        (A ⟶ homObj (R := R) G F) ≃ₗ[RingCat.sectionsSubring
          ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R).obj] (A ⊗ G ⟶ F),
      (∀ (A : SheafOfModules.{u}
          ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R))
          (φ : A ⟶ homObj (R := R) G F),
        (∀ (W : Opens X) (a : A.val.obj (op W)) (g : G.val.obj (op W)),
          (e A φ).val.app (op W)
              ((tensorObjIsoSheafification A G).inv.val.app (op W)
                (((PresheafOfModules.sheafificationAdjunction.{u}
                  (𝟙 ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R).obj)).unit.app
                  (A.val ⊗ G.val)).app (op W) (a ⊗ₜ[R.obj.obj (op W)] g))) =
            (φ.val.app (op W) a).app (op (Over.mk (𝟙 W))) g) ∧
        ∀ ψ : A ⊗ G ⟶ F,
          (∀ (W : Opens X) (a : A.val.obj (op W)) (g : G.val.obj (op W)),
            ψ.val.app (op W)
                ((tensorObjIsoSheafification A G).inv.val.app (op W)
                  (((PresheafOfModules.sheafificationAdjunction.{u}
                  (𝟙 ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R).obj)).unit.app
                    (A.val ⊗ G.val)).app (op W) (a ⊗ₜ[R.obj.obj (op W)] g))) =
              (φ.val.app (op W) a).app (op (Over.mk (𝟙 W))) g) → ψ = e A φ) ∧
      (∀ (A A' : SheafOfModules.{u}
          ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R))
          (α : A' ⟶ A) (φ : A ⟶ homObj (R := R) G F),
        e A' (α ≫ φ) = (α ⊗ₘ 𝟙 G) ≫ e A φ) := by
  let := monoidalCategory R
  let : ∀ M N : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R),
      Module (RingCat.sectionsSubring
        ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R).obj) (M ⟶ N) :=
    homModule R.obj ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R).property
  let e : ∀ A : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R),
      (A ⟶ homObj (R := R) G F) ≃ₗ[RingCat.sectionsSubring
        ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R).obj] (A ⊗ G ⟶ F) :=
    fun A ↦ { toEquiv := correspondence A G F
              map_add' := correspondence_add A G F
              map_smul' := correspondence_smul A G F }
  refine ⟨e, ?_, ?_⟩
  · intro A φ
    refine ⟨correspondence_eval A G F φ, ?_⟩
    intro ψ hψ
    apply pure_tensor_ext
    intro W a g
    exact (hψ W a g).trans (correspondence_eval A G F φ W a g).symm
  · intro A A' α φ
    exact correspondence_natural A A' G F α φ

end SheafOfModules
