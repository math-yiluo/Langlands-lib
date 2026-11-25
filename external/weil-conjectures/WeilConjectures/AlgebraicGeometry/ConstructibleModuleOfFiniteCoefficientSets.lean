/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.RingTheory.Ideal.Quotient.Basic

import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLiftHom
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison

/-!
# Module constructibility from finite sets and finite coefficients

Source: the normalization exact-sequence blueprint, unit
`proposition-proper-base-change-projective-line`, module refinement in
lem-weil-pbc-finite-pushforward-finite-stalk-module.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

-- Simultaneous local lifting of the finite list of module operations.
set_option backward.isDefEq.respectTransparency false in
private theorem finite_module_label_sections_cover
    (Λ : Type (u + 1)) [CommRing Λ] {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasSheafify J (Type (u + 1))] [J.WEqualsLocallyBijective (Type (u + 1))]
    [J.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u + 1} Λ))]
    (F : Sheaf J (ModuleCat.{u + 1} Λ)) (S : Type (u + 1)) [Finite S]
    (I : Ideal Λ) [Finite (Λ ⧸ I)]
    (hkill : ∀ (W : Cᵒᵖ) (r : Λ), r ∈ I → ∀ m : F.obj.obj W, r • m = 0)
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
  let lift : Λ ⧸ I → Λ := fun q => (Ideal.Quotient.mk_surjective q).choose
  have hlift (q : Λ ⧸ I) : Ideal.Quotient.mk I (lift q) = q :=
    (Ideal.Quotient.mk_surjective q).choose_spec
  let z : Unit ⊕ (S × S) ⊕ S ⊕ ((Λ ⧸ I) × S) → F.obj.obj (Opposite.op T) :=
    Sum.elim (fun _ ↦ 0) (Sum.elim (fun ab ↦ t T ab.1 + t T ab.2)
      (Sum.elim (fun a ↦ -t T a) (fun qa ↦ lift qa.1 • t T qa.2)))
  obtain ⟨R, hR, hl⟩ := J.exists_mem_forall_exists_toSheafify_const_app_eq S
    (fun i ↦ e.hom.hom.app (Opposite.op T) (z i))
  refine ⟨R, hR, fun W g hg hW ↦ ?_⟩
  have hnat (a : S) : t W a = F.obj.map g.op (t T a) :=
    ConcreteCategory.congr_hom (β.naturality g.op) a
  have hz (i : Unit ⊕ (S × S) ⊕ S ⊕ ((Λ ⧸ I) × S)) : ∃ a, t W a = F.obj.map g.op (z i) := by
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
    obtain ⟨b, hb⟩ := hz (Sum.inr (Sum.inr (Sum.inr (Ideal.Quotient.mk I r, a))))
    change t W b = F.obj.map g.op (lift (Ideal.Quotient.mk I r) • t T a) at hb
    rw [map_smul, ← hnat a] at hb
    refine ⟨b, hb.trans ?_⟩
    have hr : lift (Ideal.Quotient.mk I r) - r ∈ I :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (hlift _)
    have hh := hkill (Opposite.op W) _ hr (t W a)
    rw [sub_smul, sub_eq_zero] at hh
    exact hh

set_option backward.isDefEq.respectTransparency false in
private theorem finite_constant_label_submodule_neighborhood {Y : Scheme.{u}}
    (Λ : Type (u + 1)) [CommRing Λ]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Y.Etale)
    (S : Type (u + 1)) [Finite S]
    (I : Ideal Λ) [Finite (Λ ⧸ I)]
    (hkill : ∀ (W : Y.Etaleᵒᵖ) (r : Λ), r ∈ I → ∀ m : G.obj.obj W, r • m = 0)
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
    (G.over U) S I (fun W r hr m => hkill _ r hr m) e TU
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
    (Λ : Type (u + 1)) [CommRing Λ]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Y.Etale)
    (S : Type (u + 1)) [Finite S]
    (I : Ideal Λ) [Finite (Λ ⧸ I)]
    (hkill : ∀ (W : Y.Etaleᵒᵖ) (r : Λ), r ∈ I → ∀ m : G.obj.obj W, r • m = 0)
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
    finite_constant_label_submodule_neighborhood Λ G U S I hkill e x
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
    (Λ : Type (u + 1)) [CommRing Λ]
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

/-- Finite set charts refine to charts with finite constant module values when the
scalar action factors through a finite quotient ring.

Source: normalization exact-sequence blueprint, finite-operation module refinement in
`lem-weil-pbc-constructible-module-of-finite-coefficient-sets`, steps 1 and 2.
(blueprint: lem-weil-pbc-constructible-module-of-finite-coefficient-sets)

Proof: Choose the locally constant underlying-set cover and discard empty members.
The labels on a remaining member are finite: identify them with a stalk at an
algebraic closure of the residue field of a point. Choose one representative of
each element of the finite quotient Lambda/I. At the terminal object of the
localized site form the zero section, all pairwise sums and negatives of label
sections, and all scalar multiples by these finitely many representatives.
Each is a section of the constant set sheaf. The finite-section lemma supplies
a common covering sieve on which they are constant labels. A member through any
specified point has an injective label map, since the empty sieve cannot cover
an object with a point. Annihilation by I extends closure under the chosen scalar
representatives to closure under every scalar of Lambda.
The range of this label map is consequently an actual submodule of the terminal
section module. Transport its module structure to the labels using the bijection
with this range. Naturality extends the terminal linear label map to a natural
transformation from the constant module presheaf. Its underlying set map is the
sheafification unit followed by the chart isomorphism, hence locally bijective.
Sheafification therefore gives a module chart with the same finite labels.
The neighbourhoods through all points form covers; bind these to the original
cover to obtain the displayed trivialization datum and its finite module values.
On the empty scheme the covers are empty. For the unit ideal, annihilation forces
the zero module and the same construction applies. All module data here are
constructed from submodules and equivalences, never from unproved existence. -/
private theorem exists_finite_coefficient_module_charts
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)))
    (I : Ideal Λ) (hI : Finite (Λ ⧸ I))
    (hkill : ∀ (U : X.Etaleᵒᵖ) (r : Λ), r ∈ I →
      ∀ m : F.obj.obj U, r • m = 0) :
    ∃ d : LocallyConstantDatum F, ∀ i : d.cover.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty (F.over (d.cover.etalePrecoverageToEtale i) ≅
          (constantSheaf
            (X.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} Λ)).obj M) := by
  classical
  have : Finite (Λ ⧸ I) := hI
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  have : etalePrecoverage.{u}.IsStableUnderComposition :=
    inferInstanceAs (precoverage @Etale).IsStableUnderComposition
  obtain ⟨⟨𝒰₀, h𝒰₀⟩, hfinite⟩ := hF
  let 𝒰 : Cover.{u} etalePrecoverage X :=
    { I₀ := { i : 𝒰₀.I₀ // Nonempty (𝒰₀.X i) }
      X i := 𝒰₀.X i.1
      f i := 𝒰₀.f i.1
      mem₀ := by
        refine (presieve₀_mem_precoverage_iff _).mpr
          ⟨fun x => ?_, fun i => 𝒰₀.map_prop i.1⟩
        obtain ⟨i, y, hy⟩ := 𝒰₀.exists_eq x
        exact ⟨⟨i, ⟨y⟩⟩, y, hy⟩ }
  have hcharts (i : 𝒰.I₀) :
      ∃ 𝒱 : Cover.{u} etalePrecoverage (𝒰.X i), ∀ j : 𝒱.I₀,
        ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty (F.over ((MorphismProperty.Over.map ⊤ (𝒰.map_prop i)).obj
            (𝒱.etalePrecoverageToEtale j)) ≅
              (constantSheaf (X.smallEtaleTopology.over
                ((MorphismProperty.Over.map ⊤ (𝒰.map_prop i)).obj
                  (𝒱.etalePrecoverageToEtale j))) (ModuleCat.{u + 1} Λ)).obj M) := by
    let U := 𝒰.etalePrecoverageToEtale i
    have : Nonempty U.left := i.2
    have := h𝒰₀ i.1
    let H := ((sheafCompose X.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)).over U
    obtain ⟨S, ⟨e⟩⟩ := H.mem_essImage_of_isConstant
    have : Finite S := finite_constant_module_value Λ F U S e.symm fun Ω _ _ s ↦
      (ConcreteCategory.isFinitelyGenerated_iff_finite _).mp
        (hfinite.isFinitelyGenerated_sheafFiber Ω s)
    choose V v hv M hM e' α hα using
      finite_constant_module_neighborhood Λ F U S I hkill e.symm
    let 𝒱 : Cover.{u} etalePrecoverage U.left :=
      Cover.mkOfCovers U.left (fun x => (V x).left) (fun x => (V x).hom)
        (fun x => ⟨x, v x, hv x⟩) (fun x => (V x).prop)
    refine ⟨𝒱, fun x => ?_⟩
    let W : X.Etale := (MorphismProperty.Over.map ⊤ U.prop).obj (V x)
    let J := X.smallEtaleTopology.over W
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
    exact ⟨M x, hM x, ⟨((asIso
      ((presheafToSheaf J (ModuleCat.{u + 1} Λ)).map (α x))) ≪≫
        asIso ((sheafificationAdjunction J (ModuleCat.{u + 1} Λ)).counit.app H)).symm⟩⟩
  choose 𝒱 h𝒱 using hcharts
  let 𝒲 : Cover.{u} etalePrecoverage X := 𝒰.bind 𝒱
  have h𝒲 (k : 𝒲.I₀) : ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
      Nonempty (F.over (𝒲.etalePrecoverageToEtale k) ≅
        (constantSheaf (X.smallEtaleTopology.over (𝒲.etalePrecoverageToEtale k))
          (ModuleCat.{u + 1} Λ)).obj M) := by
    exact h𝒱 k.1 k.2
  let d : LocallyConstantDatum F :=
    ⟨𝒲, fun k => by
      obtain ⟨M, -, ⟨e⟩⟩ := h𝒲 k
      exact Sheaf.isConstant_of_iso _ e⟩
  exact ⟨d, h𝒲⟩


private def scalarMap (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (r : Λ) : F ⟶ F where
  hom :=
    { app := fun U => ModuleCat.ofHom (LinearMap.lsmul Λ (F.obj.obj U) r)
      naturality := by
        intro U V f
        ext m
        exact ((F.obj.map f).hom.map_smul r m).symm }

private theorem pullback_annihilated (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (I : Ideal Λ)
    (hkill : ∀ (U : X.Etaleᵒᵖ) (r : Λ), r ∈ I →
      ∀ m : F.obj.obj U, r • m = 0) :
    ∀ (U : Y.Etaleᵒᵖ) (r : Λ), r ∈ I →
      ∀ m : ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F).obj.obj U,
        r • m = 0 := by
  let L := Etale.upperStar (ModuleCat.{u + 1} Λ) f
  let R := Etale.lowerStar (ModuleCat.{u + 1} Λ) f
  let a := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
  intro U r hr m
  have hz : scalarMap Λ F r = 0 := by
    ext V x
    exact hkill V r hr x
  have he : a.homEquiv F (L.obj F) (scalarMap Λ (L.obj F) r) =
      a.homEquiv F (L.obj F) 0 := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    have hn : a.unit.app F ≫ R.map (scalarMap Λ (L.obj F) r) =
        scalarMap Λ F r ≫ a.unit.app F := by
      ext V x
      exact ((a.unit.app F).hom.app V).hom.map_smul r x |>.symm
    rw [hn, hz]
    simp
  have hzero : scalarMap Λ (L.obj F) r = 0 := (a.homEquiv F (L.obj F)).injective he
  exact congrArg (fun k => k.hom.app U m) hzero

private theorem finiteLocallyConstant_of_charts
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (d : LocallyConstantDatum F)
    (hd : ∀ i : d.cover.I₀, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
      Nonempty (F.over (d.cover.etalePrecoverageToEtale i) ≅
        (constantSheaf (X.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} Λ)).obj M)) : IsFiniteLocallyConstantSheaf F := by
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  refine { nonempty_locallyConstantDatum := ⟨d⟩,
           isFinitelyGenerated_sheafFiber := ?_ }
  intro Ω _ _ s
  obtain ⟨i, x, hx⟩ := d.cover.exists_eq (s default)
  have : Etale (d.cover.f i) := d.cover.map_prop i
  obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (d.cover.f i) s x hx
  obtain ⟨M, hM, ⟨e⟩⟩ := hd i
  let U := d.cover.etalePrecoverageToEtale i
  let ep : (Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj F ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M :=
    (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} Λ) U F).symm ≪≫
      (Etale.overSheafEquiv U (ModuleCat.{u + 1} Λ)).functor.mapIso e ≪≫
      ((Etale.overEquiv U).constantSheafSheafCongrIso
        (X.smallEtaleTopology.over U) U.left.smallEtaleTopology
        (ModuleCat.{u + 1} Λ) CategoryTheory.Over.mkIdTerminal).app M
  let es := ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) U.hom t).app F).symm ≪≫
    (pointSmallEtale t).sheafFiber.mapIso ep ≪≫
    (pointSmallEtale t).sheafFiberConstantSheafIso M
  have hfin : Finite (((pointSmallEtale (t ≫ d.cover.f i)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj F) :=
    @Finite.of_equiv _ _ hM ((CategoryTheory.forget (ModuleCat.{u + 1} Λ)).mapIso es).toEquiv.symm
  rw [ht] at hfin
  have := hfin
  exact (ModuleCat.isFinitelyGenerated_iff _).mpr Module.Finite.of_finite

/-- A sheaf annihilated by a finite-index ideal is module constructible when its
underlying set sheaf is constructible.

Source: normalization exact-sequence blueprint, module refinement in
`lem-weil-pbc-finite-pushforward-finite-stalk-module`, step 3.
(blueprint: lem-weil-pbc-constructible-module-of-finite-coefficient-sets)

Proof: The sectionwise annihilation gives every section module its canonical action
of the quotient ring, by quotient induction, and restriction maps remain linear.
Choose the finite constructible stratification and finite-set trivializing covers.
On each nonempty member, the transported addition, zero, and scalar operations are
locally constant maps on finite constant sets. For each input tuple they are locally
constant sections of the finite constant target. Refine the cover to trivialize these
sections, taking finite common refinements for all input tuples and all elements of
the finite quotient ring. Cover transitivity gives the required etale covers.
The identities for the transported operations follow from the original sheaf, yielding
constant finite quotient modules on the refinements. As Lambda-modules these are also
finite and hence finitely generated. The original stratification thus witnesses
IsConstructibleSheaf. Empty strata are discarded; the zero module and zero quotient
ring satisfy the same argument without any nontriviality assumption. -/
theorem isConstructibleSheaf_of_finite_coefficient_underlying_sets
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)))
    (I : Ideal Λ) (hI : Finite (Λ ⧸ I))
    (hkill : ∀ (U : X.Etaleᵒᵖ) (r : Λ), r ∈ I →
      ∀ m : F.obj.obj U, r • m = 0) : IsConstructibleSheaf F := by
  obtain ⟨S, hS⟩ := hF
  refine ⟨S, fun i => ?_⟩
  let G := (Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion i)).obj F
  obtain ⟨em⟩ := Etale.pullback_forget_modules_iso Λ (S.immersion i) F
  have hL : CategoryTheory.Limits.PreservesFiniteLimits
      (etaleSetPullback (S.immersion i)) := by
    unfold etaleSetPullback Functor.sheafPullbackConstruction.sheafPullback
    let : CategoryTheory.AB5OfSize.{u, u + 1} (Type (u + 1)) :=
      CategoryTheory.AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} (Type (u + 1))
    infer_instance
  obtain ⟨ea, -⟩ := etaleInverseImageAbelianLift_hom
    (S.domain i) X (S.immersion i) hL
  let e := (sheafCompose (S.domain i).smallEtaleTopology
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso em ≪≫
      ea.app ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)
  have transport {H K : Sheaf (S.domain i).smallEtaleTopology (Type (u + 1))}
      (q : H ≅ K) (hH : IsFiniteLocallyConstantSheafOfTypes H) :
      IsFiniteLocallyConstantSheafOfTypes K := by
    obtain ⟨⟨𝒰, h𝒰⟩, hfin⟩ := hH
    refine ⟨⟨𝒰, fun j ↦ ?_⟩,
      isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ s ↦ ?_⟩
    · have := h𝒰 j
      exact Sheaf.isConstant_congr _
        (((S.domain i).smallEtaleTopology.overPullback (Type (u + 1)) _).mapIso q)
    · exact @Finite.of_equiv _ _ ((ConcreteCategory.isFinitelyGenerated_iff_finite _).mp
          (hfin.isFinitelyGenerated_sheafFiber Ω s))
        ((pointSmallEtale s).sheafFiber.mapIso q).toEquiv
  have hG := transport e.symm (hS i)
  obtain ⟨d, hd⟩ := exists_finite_coefficient_module_charts Λ G hG I hI
    (pullback_annihilated Λ (S.immersion i) F I hkill)
  exact finiteLocallyConstant_of_charts Λ G d hd

end AlgebraicGeometry.Scheme
