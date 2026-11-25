/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-!
# Module sheafification commutes with tensor products

Source: Stacks Project, Modules on Sites, Tag 0GMW, lemma-sheafification-tensor
(blueprint: lem-pc-sites-module-sheafification-tensor).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace PresheafOfModules

set_option autoImplicit false

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {O : Cᵒᵖ ⥤ CommRingCat.{u}} {R : Sheaf J CommRingCat.{u}}

section Comparison

variable (α : (O ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⟶
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

set_option hygiene false in
local notation "S" => sheafification α
set_option hygiene false in
local notation "η" => (sheafificationAdjunction α).unit
set_option hygiene false in
local notation "a" => sheafification
  (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
set_option hygiene false in
local notation "ηR" => (sheafificationAdjunction
  (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit

set_option backward.isDefEq.respectTransparency false in
/-- Tensor the two module sheafification units, restricting the scalars along `α`. -/
private noncomputable def tensorSheafificationUnits
    (F G : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    F ⊗ G ⟶ (restrictScalars α).obj (((S).obj F).val ⊗ ((S).obj G).val) where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (M₃ := ((restrictScalars α).obj (((S).obj F).val ⊗ ((S).obj G).val)).obj U)
    (fun f g ↦ ((η).app F).app U f ⊗ₜ[R.obj.obj U] ((η).app G).app U g)
    (by intros; rw [map_add, TensorProduct.add_tmul])
    (by
      intro r f g
      erw [map_smul]
      change (α.app U r • (show ((S).obj F).val.obj U from ((η).app F).app U f))
        ⊗ₜ[R.obj.obj U] (show ((S).obj G).val.obj U from ((η).app G).app U g) = _
      rfl)
    (by intros; rw [map_add, TensorProduct.tmul_add])
    (by
      intro r f g
      erw [map_smul]
      change (show ((S).obj F).val.obj U from ((η).app F).app U f) ⊗ₜ[R.obj.obj U]
        (α.app U r • (show ((S).obj G).val.obj U from ((η).app G).app U g)) = _
      let : CommRing
          (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.obj U) :=
        inferInstanceAs (CommRing (R.obj.obj U))
      exact TensorProduct.tmul_smul
        (R := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.obj U)
        (α.app U r) _ _)
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro f g
    change (show ((S).obj F).val.obj V from ((η).app F).app V (F.map i f))
      ⊗ₜ[R.obj.obj V]
        (show ((S).obj G).val.obj V from ((η).app G).app V (G.map i g)) =
      (show ((S).obj F).val.obj V from ((S).obj F).val.map i (((η).app F).app U f))
        ⊗ₜ[R.obj.obj V]
          (show ((S).obj G).val.obj V from ((S).obj G).val.map i (((η).app G).app U g))
    congr 1
    · exact naturality_apply ((η).app F) i f
    · exact naturality_apply ((η).app G) i g

set_option backward.isDefEq.respectTransparency false in
/-- Sheafify the tensor of the units and identify the target with the sheaf tensor. -/
private noncomputable def sheafificationTensorComparisonApp
    (F G : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    (S).obj (F ⊗ G) ⟶
      letI := SheafOfModules.monoidalCategory R
      (S).obj F ⊗ (S).obj G := by
  let := SheafOfModules.monoidalCategory R
  let P : PresheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj :=
    ((S).obj F).val ⊗ ((S).obj G).val
  let h : P ⟶ ((a).obj P).val := (ηR).app P
  refine (sheafificationHomEquiv α).symm ?_ ≫
    (SheafOfModules.tensorObjIsoSheafification ((S).obj F) ((S).obj G)).inv
  refine tensorSheafificationUnits α F G ≫ ?_
  exact (restrictScalars α).map h

set_option backward.isDefEq.respectTransparency false in
private lemma comparisonApp_unit
    (F G : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    letI := SheafOfModules.monoidalCategory R
    (η).app (F ⊗ G) ≫
        (SheafOfModules.forget _ ⋙ restrictScalars α).map
          (sheafificationTensorComparisonApp α F G) =
      tensorSheafificationUnits α F G ≫
        (restrictScalars α).map
          ((ηR).app (((S).obj F).val ⊗ ((S).obj G).val)) ≫
        (restrictScalars α).map
          (SheafOfModules.tensorObjIsoSheafification ((S).obj F) ((S).obj G)).inv.val := by
  let := SheafOfModules.monoidalCategory R
  unfold sheafificationTensorComparisonApp
  erw [Functor.map_comp, ← Category.assoc]
  change (sheafificationHomEquiv α) ((sheafificationHomEquiv α).symm _) ≫ _ = _
  rw [Equiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma comparisonApp_tmul
    (F G : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (U : Cᵒᵖ) (f : F.obj U) (g : G.obj U) :
    (sheafificationTensorComparisonApp α F G).val.app U
        (((η).app (F ⊗ G)).app U (f ⊗ₜ[O.obj U] g)) =
      (SheafOfModules.tensorObjIsoSheafification ((S).obj F) ((S).obj G)).inv.val.app U
        (((ηR).app (((S).obj F).val ⊗ ((S).obj G).val)).app U
          (((η).app F).app U f ⊗ₜ[R.obj.obj U] ((η).app G).app U g)) := by
  have h := congrArg (fun k ↦ (k.app U).hom (f ⊗ₜ[O.obj U] g))
    (comparisonApp_unit α F G)
  exact h

set_option backward.isDefEq.respectTransparency false in
private lemma sheafifiedTensor_hom_ext
    (F G : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    {H : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    {f g : (S).obj (F ⊗ G) ⟶ H}
    (h : ∀ U (x : F.obj U) (y : G.obj U),
      f.val.app U (((η).app (F ⊗ G)).app U (x ⊗ₜ[O.obj U] y)) =
      g.val.app U (((η).app (F ⊗ G)).app U (x ⊗ₜ[O.obj U] y))) : f = g := by
  apply (sheafificationHomEquiv α).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h U x y

set_option backward.isDefEq.respectTransparency false in
private noncomputable def tensorPairing
    {P Q H : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat)}
    (h : P ⊗ Q ⟶ H) (U : Cᵒᵖ) :
    P.obj U →ₗ[O.obj U] Q.obj U →ₗ[O.obj U] H.obj U :=
  LinearMap.mk₂ (O.obj U) (fun x y ↦ h.app U (x ⊗ₜ[O.obj U] y))
    (by intros; rw [TensorProduct.add_tmul, map_add])
    (by intros; erw [← TensorProduct.smul_tmul', map_smul])
    (by intros; rw [TensorProduct.tmul_add, map_add])
    (by intros; erw [TensorProduct.tmul_smul, map_smul])

set_option backward.isDefEq.respectTransparency false in
private lemma tensorPairing_natural
    {P Q H : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat)}
    (h : P ⊗ Q ⟶ H) {U V : Cᵒᵖ} (i : U ⟶ V) (x : P.obj U) (y : Q.obj U) :
    tensorPairing h V (P.map i x) (Q.map i y) = H.map i (tensorPairing h U x y) := by
  exact naturality_apply h i (x ⊗ₜ[O.obj U] y)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def tensorPure
    (F G : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    F.val ⊗ G.val ⟶
      letI := SheafOfModules.monoidalCategory R
      (F ⊗ G).val := by
  let := SheafOfModules.monoidalCategory R
  exact (ηR).app (F.val ⊗ G.val) ≫
    (SheafOfModules.tensorObjIsoSheafification F G).inv.val

set_option backward.isDefEq.respectTransparency false in
private lemma tensorSheaf_hom_ext
    (F G : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat))
    {H : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} :
    letI := SheafOfModules.monoidalCategory R
    ∀ {f g : (S).obj F ⊗ (S).obj G ⟶ H},
      (∀ U (x : F.obj U) (y : G.obj U),
        f.val.app U ((tensorPure ((S).obj F) ((S).obj G)).app U
          (((η).app F).app U x ⊗ₜ[R.obj.obj U] ((η).app G).app U y)) =
        g.val.app U ((tensorPure ((S).obj F) ((S).obj G)).app U
          (((η).app F).app U x ⊗ₜ[R.obj.obj U] ((η).app G).app U y))) → f = g := by
  let := SheafOfModules.monoidalCategory R
  intro f g h
  let p := tensorPure ((S).obj F) ((S).obj G)
  let β := tensorPairing
    (tensorSheafificationUnits α F G ≫ (restrictScalars α).map (p ≫ f.val))
  let γf := tensorPairing (O := R.obj) (p ≫ f.val)
  let γg := tensorPairing (O := R.obj) (p ≫ g.val)
  obtain ⟨γ, _, uniq⟩ := existsUnique_bilinear_sheafification_extension
    O R α F G H β (tensorPairing_natural _)
  have hf : γf = γ := uniq γf ⟨tensorPairing_natural _, by intros; rfl⟩
  have hg : γg = γ := uniq γg ⟨tensorPairing_natural _, by
    intro U x y
    exact (h U x y).symm⟩
  have eq : γf = γg := hf.trans hg.symm
  obtain ⟨φ, _, unique⟩ := SheafOfModules.tensor_bilinear_universal R
    ((S).obj F) ((S).obj G) H γf (tensorPairing_natural _)
  apply (unique f (by intros; rfl)).trans
  symm
  apply unique g
  intro U x y
  change γg U x y = γf U x y
  rw [eq]

set_option backward.isDefEq.respectTransparency false in
private lemma comparisonApp_isIso
    (F G : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat)) :
    IsIso (sheafificationTensorComparisonApp α F G) := by
  let := SheafOfModules.monoidalCategory R
  let H := (S).obj (F ⊗ G)
  let β := tensorPairing ((η).app (F ⊗ G))
  obtain ⟨γ, hγ, _⟩ := existsUnique_bilinear_sheafification_extension
    O R α F G H β (tensorPairing_natural _)
  obtain ⟨φ, hφ, _⟩ := SheafOfModules.tensor_bilinear_universal R
    ((S).obj F) ((S).obj G) H γ hγ.1
  have hφ' : ∀ U (x : F.obj U) (y : G.obj U),
      φ.val.app U ((tensorPure ((S).obj F) ((S).obj G)).app U
        (((η).app F).app U x ⊗ₜ[R.obj.obj U] ((η).app G).app U y)) =
      ((η).app (F ⊗ G)).app U (x ⊗ₜ[O.obj U] y) := by
    intro U x y
    exact (hφ U _ _).trans (hγ.2 U x y)
  refine ⟨⟨φ, ?_, ?_⟩⟩
  · apply sheafifiedTensor_hom_ext α F G
    intro U x y
    change φ.val.app U ((sheafificationTensorComparisonApp α F G).val.app U
      (((η).app (F ⊗ G)).app U (x ⊗ₜ[O.obj U] y))) = _
    rw [comparisonApp_tmul]
    exact hφ' U x y
  · apply tensorSheaf_hom_ext α F G
    intro U x y
    change (sheafificationTensorComparisonApp α F G).val.app U
      (φ.val.app U ((tensorPure ((S).obj F) ((S).obj G)).app U
        (((η).app F).app U x ⊗ₜ[R.obj.obj U] ((η).app G).app U y))) = _
    rw [hφ']
    exact comparisonApp_tmul α F G U x y


set_option backward.isDefEq.respectTransparency false in
private lemma tensorIso_natural
    {F F' G G' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    letI := SheafOfModules.monoidalCategory R
    (f ⊗ₘ g) ≫ (SheafOfModules.tensorObjIsoSheafification F' G').hom =
      (SheafOfModules.tensorObjIsoSheafification F G).hom ≫
        (a).map (f.val ⊗ₘ g.val) := by
  let := SheafOfModules.monoidalCategory R
  erw [tensorHom_def, Category.assoc,
    SheafOfModules.whiskerLeft_tensorObjIsoSheafification_hom (R := R) F' g,
    ← Category.assoc,
    SheafOfModules.whiskerRight_tensorObjIsoSheafification_hom (R := R) f G,
    Category.assoc, ← Functor.map_comp, ← tensorHom_def]

set_option backward.isDefEq.respectTransparency false in
private lemma tensorPure_natural
    {F F' G G' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    letI := SheafOfModules.monoidalCategory R
    tensorPure F G ≫ (f ⊗ₘ g).val =
      (f.val ⊗ₘ g.val) ≫ tensorPure F' G' := by
  let := SheafOfModules.monoidalCategory R
  have h : (SheafOfModules.tensorObjIsoSheafification F G).inv ≫ (f ⊗ₘ g) =
      (a).map (f.val ⊗ₘ g.val) ≫
        (SheafOfModules.tensorObjIsoSheafification F' G').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← tensorIso_natural, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hval := congrArg SheafOfModules.Hom.val h
  change (SheafOfModules.tensorObjIsoSheafification F G).inv.val ≫ (f ⊗ₘ g).val =
    ((a).map (f.val ⊗ₘ g.val)).val ≫
      (SheafOfModules.tensorObjIsoSheafification F' G').inv.val at hval
  have hn := (ηR).naturality (f.val ⊗ₘ g.val)
  change (f.val ⊗ₘ g.val) ≫ (ηR).app (F'.val ⊗ G'.val) =
    (ηR).app (F.val ⊗ G.val) ≫ ((a).map (f.val ⊗ₘ g.val)).val at hn
  unfold tensorPure
  erw [Category.assoc, hval, ← Category.assoc, ← hn]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma tensorUnits_natural
    {F F' G G' : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat)}
    (f : F ⟶ F') (g : G ⟶ G') :
    (f ⊗ₘ g) ≫ tensorSheafificationUnits α F' G' =
      tensorSheafificationUnits α F G ≫
        (restrictScalars α).map (((S).map f).val ⊗ₘ ((S).map g).val) := by
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  have hf := congrArg (fun k ↦ (k.app U).hom x) ((η).naturality f)
  have hg := congrArg (fun k ↦ (k.app U).hom y) ((η).naturality g)
  change ((η).app F').app U (f.app U x) =
    ((S).map f).val.app U (((η).app F).app U x) at hf
  change ((η).app G').app U (g.app U y) =
    ((S).map g).val.app U (((η).app G).app U y) at hg
  change (show ((S).obj F').val.obj U from ((η).app F').app U (f.app U x))
      ⊗ₜ[R.obj.obj U]
        (show ((S).obj G').val.obj U from ((η).app G').app U (g.app U y)) =
    ((S).map f).val.app U (((η).app F).app U x) ⊗ₜ[R.obj.obj U]
      ((S).map g).val.app U (((η).app G).app U y)
  exact congrArg₂ (fun x y ↦ x ⊗ₜ[R.obj.obj U] y) hf hg

set_option backward.isDefEq.respectTransparency false in
private lemma comparisonApp_unit'
    (F G : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat)) :
    letI := SheafOfModules.monoidalCategory R
    (η).app (F ⊗ G) ≫
        (SheafOfModules.forget _ ⋙ restrictScalars α).map
          (sheafificationTensorComparisonApp α F G) =
      tensorSheafificationUnits α F G ≫
        (restrictScalars α).map (tensorPure ((S).obj F) ((S).obj G)) := by
  let := SheafOfModules.monoidalCategory R
  have h := comparisonApp_unit α F G
  unfold tensorPure
  erw [Functor.map_comp]
  exact h

set_option backward.isDefEq.respectTransparency false in
private lemma comparisonApp_natural
    {F F' G G' : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat)}
    (f : F ⟶ F') (g : G ⟶ G') :
    letI := SheafOfModules.monoidalCategory R
    (S).map (f ⊗ₘ g) ≫ sheafificationTensorComparisonApp α F' G' =
      sheafificationTensorComparisonApp α F G ≫ ((S).map f ⊗ₘ (S).map g) := by
  let := SheafOfModules.monoidalCategory R
  let B := SheafOfModules.forget _ ⋙ restrictScalars α
  have hn := (η).naturality (f ⊗ₘ g)
  change (f ⊗ₘ g) ≫ (η).app (F' ⊗ G') =
    (η).app (F ⊗ G) ≫ B.map ((S).map (f ⊗ₘ g)) at hn
  have h1 := comparisonApp_unit' α F G
  have h2 := comparisonApp_unit' α F' G'
  have h3 := tensorUnits_natural α f g
  have h4 := congrArg ((restrictScalars α).map)
    (tensorPure_natural ((S).map f) ((S).map g))
  apply (sheafificationHomEquiv α).injective
  change (η).app (F ⊗ G) ≫ B.map (_ ≫ _) =
    (η).app (F ⊗ G) ≫ B.map (_ ≫ _)
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc,
    ← hn]
  rw [Category.assoc]
  erw [h2, ← Category.assoc, h3, Category.assoc, ← Functor.map_comp]
  erw [← h4, Functor.map_comp, ← Category.assoc, ← h1]
  rfl


end Comparison

/-- The canonical tensor comparison is an isomorphism, natural in both presheaf modules.
The locally bijective ring map identifies `R` with the sheafification of `O`. The displayed
pure-tensor identity specifies the canonical comparison, using the sheafification units.
Source: Stacks Project, Tag 0GMW (blueprint: lem-pc-sites-module-sheafification-tensor).

Proof:
1. Sectionwise pure tensors of the module sheafification maps define a balanced map from
   the presheaf tensor to the tensor of the associated modules. The action and linearity
   come from lem-pc-sites-module-sheafification-interface.
2. Sheafify this map using the interface and def-pur-sheaf-tensor-product to obtain the
   morphism from the sheafified presheaf tensor to the sheaf tensor.
3. Extend the original pure-tensor pairing uniquely to the associated modules, using
   lem-pc-sites-module-sheafification-bilinear-extension. The universal property in
   lem-pc-sites-sheaf-tensor-bilinear-universal gives the inverse morphism.
4. Precompose both composites with the sheafification units. They agree with identities
   on pure tensors. Uniqueness of sheafification and of bilinear extension makes both
   composites identities. The same characterization commutes with morphisms in both
   factors, giving the natural isomorphism and the displayed pure-tensor identity. -/
theorem exists_sheafificationTensorIso
    (α : (O ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⟶
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    letI := SheafOfModules.monoidalCategory R
    ∃ e : (sheafification α).prod (sheafification α) ⋙ tensor _ ≅
        tensor (PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u})) ⋙
          sheafification α,
      ∀ (F G : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
        (U : Cᵒᵖ) (f : F.obj U) (g : G.obj U),
        (e.inv.app (F, G)).val.app U
          (((sheafificationAdjunction α).unit.app (F ⊗ G)).app U
            (f ⊗ₜ[O.obj U] g)) =
        (SheafOfModules.tensorObjIsoSheafification
          ((sheafification α).obj F) ((sheafification α).obj G)).inv.val.app U
            (((sheafificationAdjunction
              (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.app
              (((sheafification α).obj F).val ⊗ ((sheafification α).obj G).val)).app U
                ((((sheafificationAdjunction α).unit.app F).app U f) ⊗ₜ[R.obj.obj U]
                  (((sheafificationAdjunction α).unit.app G).app U g))) := by
  let := SheafOfModules.monoidalCategory R
  let c : tensor _ ⋙ sheafification α ⟶
      (sheafification α).prod (sheafification α) ⋙ tensor _ :=
    { app := fun FG ↦ sheafificationTensorComparisonApp α FG.1 FG.2
      naturality := fun {X Y} f ↦ comparisonApp_natural α f.1 f.2 }
  have : IsIso c := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro FG
    exact comparisonApp_isIso α FG.1 FG.2
  refine ⟨(asIso c).symm, ?_⟩
  intro F G U f g
  exact comparisonApp_tmul α F G U f g

/-- With an already sheafified first factor, tensoring commutes with module sheafification,
including restriction of scalars along the ring sheafification map. The isomorphism of
bifunctors expresses naturality in the sheaf and the presheaf simultaneously.
Source: Stacks Project, Tag 0GMW (blueprint: lem-pc-sites-module-sheafification-tensor).

Proof: apply the preceding comparison to the restricted underlying presheaf of `G` and
`F`. The counit of lem-pc-sites-module-sheafification-interface identifies the associated
module of the restricted `G` with `G`: its underlying abelian sheaf is the sheafification
of a sheaf, hence its unit is invertible by def-weil-pbc-sheafification. The inverse is
linear by the interface's factorization property. Substitute this counit isomorphism in
Step 4's tensor comparison. Naturality of the counit and that comparison gives naturality
in `G` and `F`. -/
theorem nonempty_sheafTensorSheafificationIso
    (α : (O ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⟶
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    letI := SheafOfModules.monoidalCategory R
    Nonempty
      ((𝟭 (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))).prod
          (sheafification α) ⋙ tensor _ ≅
        ((SheafOfModules.forget _ ⋙ restrictScalars α).prod
          (𝟭 (PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u})))) ⋙
            tensor _ ⋙ sheafification α) := by
  let := SheafOfModules.monoidalCategory R
  obtain ⟨e, _⟩ := exists_sheafificationTensorIso α
  let B := SheafOfModules.forget _ ⋙ restrictScalars α
  let S := sheafification α
  let c : B ⋙ S ≅ 𝟭 _ := asIso (sheafificationAdjunction α).counit
  refine ⟨?_⟩
  exact (Functor.isoWhiskerRight (NatIso.prod c.symm (Iso.refl S)) (tensor _)) ≪≫
    Functor.isoWhiskerLeft (B.prod (𝟭 _)) e


end PresheafOfModules
