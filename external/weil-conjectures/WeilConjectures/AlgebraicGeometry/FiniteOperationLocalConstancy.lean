/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Sites.Adjunction

import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-! The finite operation refinement needed for local constancy of module sheaves.
(blueprint: lem-pod-module-local-constancy-of-finite-underlying-operation-compatible-cover)
-/

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry.Scheme

-- Simultaneous local lifting of the finite list of module operations.
set_option backward.isDefEq.respectTransparency false in
private theorem finite_module_label_sections_cover
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ] {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasSheafify J (Type (u + 1))] [J.WEqualsLocallyBijective (Type (u + 1))]
    [J.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u + 1} Λ))]
    (F : Sheaf J (ModuleCat.{u + 1} Λ)) (S : Type (u + 1)) [Finite S]
    (e : (sheafCompose J (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj F ≅
      (constantSheaf J (Type (u + 1))).obj S) (T : C) :
    ∃ R ∈ J T, ∀ (W : C) (g : W ⟶ T), R g → (⊥ : Sieve W) ∉ J W →
      let β := toSheafify J ((Functor.const Cᵒᵖ).obj S) ≫ e.inv.hom
      let t : S → F.obj.obj (Opposite.op W) := fun s ↦ β.app (Opposite.op W) s
      Function.Injective t ∧ (∃ s, t s = 0) ∧
        (∀ a b, ∃ c, t c = t a + t b) ∧ (∀ a, ∃ b, t b = -t a) ∧
        (∀ (r : Λ) a, ∃ b, t b = r • t a) := by
  classical
  let β := toSheafify J ((Functor.const Cᵒᵖ).obj S) ≫ e.inv.hom
  let t : ∀ W : C, S → F.obj.obj (Opposite.op W) := fun W s ↦ β.app (Opposite.op W) s
  let z : Unit ⊕ (S × S) ⊕ S ⊕ (Λ × S) → F.obj.obj (Opposite.op T) :=
    Sum.elim (fun _ ↦ 0) (Sum.elim (fun ab ↦ t T ab.1 + t T ab.2)
      (Sum.elim (fun a ↦ -t T a) (fun qa ↦ qa.1 • t T qa.2)))
  obtain ⟨R, hR, hl⟩ := J.exists_mem_forall_exists_toSheafify_const_app_eq S
    (fun i ↦ e.hom.hom.app (Opposite.op T) (z i))
  refine ⟨R, hR, fun W g hg hW ↦ ?_⟩
  have hnat (a : S) : t W a = F.obj.map g.op (t T a) :=
    ConcreteCategory.congr_hom (β.naturality g.op) a
  have hz (i : Unit ⊕ (S × S) ⊕ S ⊕ (Λ × S)) : ∃ a, t W a = F.obj.map g.op (z i) := by
    obtain ⟨a, ha⟩ := hl g hg i
    refine ⟨a, ?_⟩
    have hea := congrArg (fun y ↦ e.inv.hom.app (Opposite.op W) y) ha
    have hn := ConcreteCategory.congr_hom (e.inv.hom.naturality g.op)
      (e.hom.hom.app (Opposite.op T) (z i))
    have hid := Iso.hom_inv_id_app_apply ((sheafToPresheaf J (Type (u + 1))).mapIso e)
      (Opposite.op T) (z i)
    change e.inv.hom.app (Opposite.op T) (e.hom.hom.app (Opposite.op T) (z i)) = z i at hid
    simp only [ConcreteCategory.comp_apply, hid] at hn
    exact hea.trans hn
  have hi : Function.Injective (t W) := by
    intro a b hab
    apply J.toSheafify_const_app_injective S hW
    have hh := congrArg (fun y ↦ e.hom.hom.app (Opposite.op W) y) hab
    have hid (s : S) := Iso.inv_hom_id_app_apply
      ((sheafToPresheaf J (Type (u + 1))).mapIso e) (Opposite.op W)
        ((toSheafify J ((Functor.const Cᵒᵖ).obj S)).app (Opposite.op W) s)
    change ∀ s : S, e.hom.hom.app (Opposite.op W) (t W s) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj S)).app (Opposite.op W) s at hid
    simpa only [hid] using hh
  refine ⟨hi, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hz (Sum.inl ())
    exact ⟨a, by simpa [z, t, β] using ha⟩
  · intro a b
    obtain ⟨c, hc⟩ := hz (Sum.inr (Sum.inl (a, b)))
    change t W c = F.obj.map g.op (t T a + t T b) at hc
    rw [map_add, ← hnat a, ← hnat b] at hc
    exact ⟨c, hc⟩
  · intro a
    obtain ⟨b, hb⟩ := hz (Sum.inr (Sum.inr (Sum.inl a)))
    change t W b = F.obj.map g.op (-t T a) at hb
    rw [map_neg, ← hnat a] at hb
    exact ⟨b, hb⟩
  · intro r a
    obtain ⟨b, hb⟩ := hz (Sum.inr (Sum.inr (Sum.inr (r, a))))
    change t W b = F.obj.map g.op (r • t T a) at hb
    rw [map_smul, ← hnat a] at hb
    exact ⟨b, hb⟩


set_option backward.isDefEq.respectTransparency false in
private theorem finite_constant_label_submodule_neighborhood {Y : Scheme.{u}}
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Y.Etale)
    (S : Type (u + 1)) [Finite S]
    (e : ((sheafCompose Y.smallEtaleTopology
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G).over U ≅
        (constantSheaf (Y.smallEtaleTopology.over U) (Type (u + 1))).obj S)
    (x : U.left) :
    ∃ (V : U.left.Etale) (v : V.left), V.hom v = x ∧
      ∃ e' : (constantSheaf
          (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
          (Type (u + 1))).obj S ≅
            (sheafCompose
              (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
              (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
                (G.over ((MorphismProperty.Over.map ⊤ U.prop).obj V)),
          let β := toSheafify
            (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
            ((Functor.const
              (Over ((MorphismProperty.Over.map ⊤ U.prop).obj V))ᵒᵖ).obj
                S) ≫ e'.hom.hom
          let T := (G.over
            ((MorphismProperty.Over.map ⊤ U.prop).obj V)).obj.obj
              (Opposite.op (Over.mk (𝟙 ((MorphismProperty.Over.map ⊤ U.prop).obj V))))
          let t : S → T := fun s ↦ β.app
            (Opposite.op (Over.mk (𝟙 ((MorphismProperty.Over.map ⊤ U.prop).obj V)))) s
          Function.Injective t ∧ (∃ s, t s = 0) ∧
            (∀ a b, ∃ c, t c = t a + t b) ∧ (∀ a, ∃ b, t b = -t a) ∧
        (∀ (r : Λ) a, ∃ b, t b = r • t a) := by
  classical
  let J := Y.smallEtaleTopology
  let TU : Over U := Over.mk (𝟙 U)
  obtain ⟨R, hR, hl⟩ := finite_module_label_sections_cover Λ (J.over U)
    (G.over U) S e TU
  have hRY : (Sieve.overEquiv TU R) ∈ J U := (J.mem_over_iff R).mp hR
  obtain ⟨𝒰, h𝒰, hp, hle⟩ := (mem_smallGrothendieckTopology U _).mp hRY
  let := h𝒰
  obtain ⟨i, v, hv⟩ := 𝒰.exists_eq x
  let B : Y.Etale := (𝒰.X i).asOverProp Y (hp i)
  let fB : B ⟶ U := (𝒰.f i).asOverProp Y
  have hfB : Sieve.overEquiv TU R fB := hle _ _ ⟨i⟩
  let V : U.left.Etale := 𝒰.etalePrecoverageToEtale i
  let A : Y.Etale := (MorphismProperty.Over.map ⊤ U.prop).obj V
  let fA : A ⟶ U := MorphismProperty.Over.homMk V.hom
  let k : A ⟶ B := MorphismProperty.Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫ (𝒰.X i ↘ Y) = 𝒰.f i ≫ U.hom
    simp only [Category.id_comp]
    exact (HomIsOver.comp_over (f := 𝒰.f i) (S := Y)).symm)
  have hfac : k ≫ fB = fA := by
    apply MorphismProperty.Over.Hom.ext
    change 𝟙 _ ≫ 𝒰.f i = 𝒰.f i
    exact Category.id_comp _
  have hfA : Sieve.overEquiv TU R fA := by
    rw [← hfac]
    exact (Sieve.overEquiv TU R).downward_closed hfB k
  have hR' : R (Over.homMk fA : Over.mk (fA ≫ 𝟙 U) ⟶ TU) :=
    (Sieve.overEquiv_iff R fA).mp hfA
  have hnon : (⊥ : Sieve A) ∉ J A := by
    intro hbot
    obtain ⟨𝒲, _, hpW, hleW⟩ := (mem_smallGrothendieckTopology A _).mp hbot
    obtain ⟨j, w, hw⟩ := 𝒲.exists_eq v
    exact hleW _ _ ⟨j⟩
  have hnon' : (⊥ : Sieve (Over.mk (fA ≫ 𝟙 U))) ∉
      (J.over U) (Over.mk (fA ≫ 𝟙 U)) := by
    intro hb
    apply hnon
    have hh := (J.mem_over_iff _).mp hb
    rw [(Sieve.overEquiv (Over.mk (fA ≫ 𝟙 U))).map_bot] at hh
    exact hh
  have hclosed := hl _ (Over.homMk fA) hR' hnon'
  let L := Over.map fA
  let c := (L.pushforwardContinuousSheafificationCompatibility (Type (u + 1))
    (J.over A) (J.over U)).app ((Functor.const (Over U)ᵒᵖ).obj S)
  let eS : (constantSheaf (J.over A) (Type (u + 1))).obj S ≅
      (sheafCompose (J.over A) (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
        (G.over A) :=
    c ≪≫ (J.overMapPullback (Type (u + 1)) fA).mapIso e.symm ≪≫
      Sheaf.pushforwardOverMapIso
        ((sheafCompose J (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G) fA
  refine ⟨V, v, hv, eS, ?_⟩
  have hunit := L.toSheafify_pullbackSheafificationCompatibility
    (Type (u + 1)) (J.over A) (J.over U) ((Functor.const (Over U)ᵒᵖ).obj S)
  have hlabel (s : S) :
      (toSheafify (J.over A) ((Functor.const (Over A)ᵒᵖ).obj S) ≫
        eS.hom.hom).app (Opposite.op (Over.mk (𝟙 A))) s =
      (toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj S) ≫
        e.inv.hom).app (Opposite.op (Over.mk (fA ≫ 𝟙 U))) s := by
    simp only [eS, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      NatTrans.comp_app, ConcreteCategory.comp_apply]
    change e.inv.hom.app (L.op.obj (Opposite.op (Over.mk (𝟙 A))))
      ((toSheafify (J.over A) ((Functor.const (Over A)ᵒᵖ).obj S) ≫
        c.hom.hom).app (Opposite.op (Over.mk (𝟙 A))) s) = _
    have hh := ConcreteCategory.congr_hom
      (NatTrans.congr_app hunit (Opposite.op (Over.mk (𝟙 A)))) s
    change (toSheafify (J.over A) ((Functor.const (Over A)ᵒᵖ).obj S) ≫
      c.hom.hom).app (Opposite.op (Over.mk (𝟙 A))) s =
      (toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj S)).app
        (L.op.obj (Opposite.op (Over.mk (𝟙 A)))) s at hh
    refine (congrArg (fun z ↦ e.inv.hom.app
      (L.op.obj (Opposite.op (Over.mk (𝟙 A)))) z) hh).trans ?_
    change e.inv.hom.app (Opposite.op (Over.mk (𝟙 A ≫ fA)))
      ((toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj S)).app
        (Opposite.op (Over.mk (𝟙 A ≫ fA))) s) = _
    let φ : (A ⟶ U) → G.obj.obj (Opposite.op A) := fun f ↦
      e.inv.hom.app (Opposite.op (Over.mk f))
        ((toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj S)).app
          (Opposite.op (Over.mk f)) s)
    exact congrArg φ (show 𝟙 A ≫ fA = fA ≫ 𝟙 U by simp)
  let tnew : S → G.obj.obj (Opposite.op A) := fun s ↦
    (toSheafify (J.over A) ((Functor.const (Over A)ᵒᵖ).obj S) ≫
      eS.hom.hom).app (Opposite.op (Over.mk (𝟙 A))) s
  let told : S → G.obj.obj (Opposite.op A) := fun s ↦
    (toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj S) ≫
      e.inv.hom).app (Opposite.op (Over.mk (fA ≫ 𝟙 U))) s
  change Function.Injective tnew ∧ (∃ s, tnew s = 0) ∧
    (∀ a b, ∃ d, tnew d = tnew a + tnew b) ∧ (∀ a, ∃ b, tnew b = -tnew a) ∧
      (∀ (r : Λ) a, ∃ b, tnew b = r • tnew a)
  have ht : tnew = told := funext hlabel
  rw [ht]
  exact hclosed


private theorem finite_constant_module_neighborhood {Y : Scheme.{u}}
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Y.Etale)
    (S : Type (u + 1)) [Finite S]
    (e : ((sheafCompose Y.smallEtaleTopology
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G).over U ≅
        (constantSheaf (Y.smallEtaleTopology.over U) (Type (u + 1))).obj S)
    (x : U.left) :
    ∃ (V : U.left.Etale) (v : V.left), V.hom v = x ∧
      ∃ (M : (ModuleCat.{u + 1} Λ)), Finite M ∧
        ∃ e' : (constantSheaf
          (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
          (Type (u + 1))).obj (M : Type (u + 1)) ≅
            (sheafCompose
              (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
              (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
                (G.over ((MorphismProperty.Over.map ⊤ U.prop).obj V)),
          ∃ α : (Functor.const
            (Over ((MorphismProperty.Over.map ⊤ U.prop).obj V))ᵒᵖ).obj M ⟶
              (G.over ((MorphismProperty.Over.map ⊤ U.prop).obj V)).obj,
            Functor.whiskerRight α (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) =
              toSheafify
                (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
                ((Functor.const
                  (Over ((MorphismProperty.Over.map ⊤ U.prop).obj V))ᵒᵖ).obj
                    (M : Type (u + 1))) ≫ e'.hom.hom := by
  classical
  -- Use local closure of the finite label sections, then transport their subgroup structure.
  obtain ⟨V, v, hv, e', hinj, hzero, hadd, hneg, hsmul⟩ :=
    finite_constant_label_submodule_neighborhood Λ G U S e x
  let A := (MorphismProperty.Over.map ⊤ U.prop).obj V
  let F := G.over A
  let T := F.obj.obj (Opposite.op (Over.mk (𝟙 A)))
  let t : S → T := fun s ↦
    (toSheafify (Y.smallEtaleTopology.over A)
      ((Functor.const (Over A)ᵒᵖ).obj S) ≫ e'.hom.hom).app
        (Opposite.op (Over.mk (𝟙 A))) s
  let H : Submodule Λ T :=
    { carrier := Set.range t
      zero_mem' := hzero
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact hadd a b
      smul_mem' := by
        rintro r _ ⟨a, rfl⟩
        exact hsmul r a }
  let q : S ≃ H := Equiv.ofBijective (fun s ↦ ⟨t s, ⟨s, rfl⟩⟩)
    ⟨fun a b h ↦ hinj (congrArg Subtype.val h), by
      rintro ⟨z, a, rfl⟩
      exact ⟨a, rfl⟩⟩
  let : AddCommGroup S := q.addCommGroup
  let : Module Λ S := q.addEquiv.module Λ
  let M : ModuleCat.{u + 1} Λ := ModuleCat.of Λ S
  let η : M →ₗ[Λ] T := H.subtype.comp (q.addEquiv.linearEquiv Λ).toLinearMap
  have hM : Finite M := inferInstance
  let β := toSheafify
    (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
    ((Functor.const
      (Over ((MorphismProperty.Over.map ⊤ U.prop).obj V))ᵒᵖ).obj
        (M : Type (u + 1))) ≫ e'.hom.hom
  let α : (Functor.const
      (Over ((MorphismProperty.Over.map ⊤ U.prop).obj V))ᵒᵖ).obj M ⟶
        (G.over ((MorphismProperty.Over.map ⊤ U.prop).obj V)).obj :=
    { app := fun W ↦ ModuleCat.ofHom
        { toFun := β.app W
          map_add' := by
            intro a b
            have hnat (m : M) := ConcreteCategory.congr_hom
              (β.naturality (Over.mkIdTerminal.from W.unop).op) m
            change ∀ m : M, β.app W m =
              (F.obj.map (Over.mkIdTerminal.from W.unop).op) (t m) at hnat
            rw [hnat, hnat, hnat]
            change (F.obj.map (Over.mkIdTerminal.from W.unop).op) (η (a + b)) =
              (F.obj.map (Over.mkIdTerminal.from W.unop).op) (η a) +
                (F.obj.map (Over.mkIdTerminal.from W.unop).op) (η b)
            simp
          map_smul' := by
            intro r a
            have hnat (m : M) := ConcreteCategory.congr_hom
              (β.naturality (Over.mkIdTerminal.from W.unop).op) m
            change ∀ m : M, β.app W m =
              (F.obj.map (Over.mkIdTerminal.from W.unop).op) (t m) at hnat
            rw [hnat, hnat]
            change (F.obj.map (Over.mkIdTerminal.from W.unop).op) (η (r • a)) =
              r • (F.obj.map (Over.mkIdTerminal.from W.unop).op) (η a)
            simp }
      naturality := by
        intro W W' f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        exact ConcreteCategory.congr_hom (β.naturality f) m }
  refine ⟨V, v, hv, M, hM, e', α, ?_⟩
  rfl


private theorem finite_constant_module_value {Y : Scheme.{u}}
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Y.Etale)
    (S : Type (u + 1))
    (e : ((sheafCompose Y.smallEtaleTopology
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G).over U ≅
        (constantSheaf (Y.smallEtaleTopology.over U) (Type (u + 1))).obj S)
    (hfinite : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Finite (((pointSmallEtale s).sheafFiber (A := Type (u + 1))).obj
        ((sheafCompose Y.smallEtaleTopology
          (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G)))
    [Nonempty U.left] : Finite S := by
  classical
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))
  let x : U.left := Classical.arbitrary _
  let s := U.left.algClosurePoint x
  let E := (Etale.overSheafEquiv U (ModuleCat.{u + 1} Λ)).functor
  let es : (sheafCompose U.left.smallEtaleTopology
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj (E.obj (G.over U)) ≅
      (constantSheaf U.left.smallEtaleTopology (Type (u + 1))).obj S :=
    (Etale.overSheafEquiv U (Type (u + 1))).functor.mapIso e ≪≫
      ((Etale.overEquiv U).constantSheafSheafCongrIso
        (Y.smallEtaleTopology.over U) U.left.smallEtaleTopology
        (Type (u + 1)) CategoryTheory.Over.mkIdTerminal).app S
  let eG := (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} Λ) U G).symm
  let eStalk := ((pointSmallEtale (s ≫ U.hom)).sheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app G ≪≫
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ)).mapIso
      (((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) U.hom s).app G).symm ≪≫
        (pointSmallEtale s).sheafFiber.mapIso eG) ≪≫
    (((pointSmallEtale s).sheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app (E.obj (G.over U))).symm ≪≫
    (pointSmallEtale s).sheafFiber.mapIso es ≪≫
    (pointSmallEtale s).sheafFiberConstantSheafIso S
  exact @Finite.of_equiv _ _ (hfinite _ (s ≫ U.hom)) eStalk.toEquiv

/-- The module operations lift an underlying constant trivialization.

Source: Stacks Project, Tag 0DV5, proof of (2)--(3), using Tag 093S (1).  Starting
from a cover on which the underlying sheaf of sets is constant, refine it successively
for addition, zero, negation, and scalar multiplication (there are finitely many
scalars).  The resulting constant maps satisfy the module identities after evaluation
at a geometric point, and hence give a constant sheaf of modules on every member.
The finite geometric-stalk hypothesis makes every constant model on a nonempty
member finite. Discard empty covering members. Refine the finite list of operation
sections, form their range as a submodule, and transport that actual submodule structure
to the finite labels. The resulting linear map from the constant presheaf is locally
bijective, so sheafification is an isomorphism. Bind these covers to the original cover.
No module data are chosen from an unproved existence theorem.
(blueprint: lem-pod-module-local-constancy-of-finite-underlying-operation-compatible-cover) -/
theorem module_operationCompatibleCover
    {Y : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (hG : G = (sheafForget Y.smallEtaleTopology).obj F)
    (hfinite : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Finite (((pointSmallEtale s).sheafFiber (A := Type (u + 1))).obj G))
    (𝒰 : Cover.{u} etalePrecoverage Y)
    (h𝒰 : ∀ i : 𝒰.I₀,
      (G.over (𝒰.etalePrecoverageToEtale i)).IsConstant
        (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))) :
    IsLocallyConstantSheaf F := by
  classical
  subst G
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  have : etalePrecoverage.{u}.IsStableUnderComposition :=
    inferInstanceAs (precoverage @Etale).IsStableUnderComposition
  let 𝒰' : Cover.{u} etalePrecoverage Y :=
    { I₀ := { i : 𝒰.I₀ // Nonempty (𝒰.X i) }
      X i := 𝒰.X i.1
      f i := 𝒰.f i.1
      mem₀ := by
        refine (presieve₀_mem_precoverage_iff _).mpr
          ⟨fun y ↦ ?_, fun i ↦ 𝒰.map_prop i.1⟩
        obtain ⟨i, x, hx⟩ := 𝒰.exists_eq y
        exact ⟨⟨i, ⟨x⟩⟩, x, hx⟩ }
  have hrefine (i : 𝒰'.I₀) : ∃ 𝒱 : Cover.{u} etalePrecoverage (𝒰'.X i),
      ∀ j : 𝒱.I₀,
        (F.over ((MorphismProperty.Over.map ⊤ (𝒰'.map_prop i)).obj
          (𝒱.etalePrecoverageToEtale j))).IsConstant
            (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ (𝒰'.map_prop i)).obj
              (𝒱.etalePrecoverageToEtale j))) := by
    let U := 𝒰'.etalePrecoverageToEtale i
    have : Nonempty U.left := i.2
    have := h𝒰 i.1
    obtain ⟨S, ⟨e⟩⟩ :=
      (((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj F).over U).mem_essImage_of_isConstant
    have : Finite S := finite_constant_module_value Λ F U S e.symm hfinite
    choose V v hv M hM e' α hα using finite_constant_module_neighborhood Λ F U S e.symm
    let 𝒱 : Cover.{u} etalePrecoverage U.left :=
      Cover.mkOfCovers U.left (fun x ↦ (V x).left) (fun x ↦ (V x).hom)
        (fun x ↦ ⟨x, v x, hv x⟩) (fun x ↦ (V x).prop)
    refine ⟨𝒱, fun x ↦ ?_⟩
    let W : Y.Etale := (MorphismProperty.Over.map ⊤ U.prop).obj (V x)
    let J := Y.smallEtaleTopology.over W
    let H := F.over W
    have : IsIso (e' x).hom.hom :=
      inferInstanceAs (IsIso ((sheafToPresheaf J (Type (u + 1))).map (e' x).hom))
    have hi : Presheaf.IsLocallyInjective J (α x) := by
      rw [← Presheaf.isLocallyInjective_forget_iff, hα x]
      have ht : Presheaf.IsLocallyInjective J (toSheafify J
          ((Functor.const (Over W)ᵒᵖ).obj (M x : Type (u + 1)))) := inferInstance
      exact Presheaf.isLocallyInjective_comp J _ _
    have hs : Presheaf.IsLocallySurjective J (α x) := by
      rw [Presheaf.isLocallySurjective_iff_whisker_forget, hα x]
      have ht : Presheaf.IsLocallySurjective J (toSheafify J
          ((Functor.const (Over W)ᵒᵖ).obj (M x : Type (u + 1)))) := inferInstance
      exact Presheaf.isLocallySurjective_comp (J := J)
        (toSheafify J ((Functor.const (Over W)ᵒᵖ).obj (M x : Type (u + 1))))
        (e' x).hom.hom
    have hw : J.W (α x) := J.W_of_isLocallyBijective (α x)
    have : IsIso ((presheafToSheaf J (ModuleCat.{u + 1} Λ)).map (α x)) :=
      (J.W_iff (α x)).mp hw
    exact Sheaf.isConstant_of_iso J
      ((asIso ((presheafToSheaf J (ModuleCat.{u + 1} Λ)).map (α x))) ≪≫
        asIso ((sheafificationAdjunction J (ModuleCat.{u + 1} Λ)).counit.app H)).symm
  choose 𝒱 h𝒱 using hrefine
  refine ⟨⟨⟨𝒰'.bind 𝒱, fun i ↦ ?_⟩⟩⟩
  exact h𝒱 i.1 i.2


end AlgebraicGeometry.Scheme
