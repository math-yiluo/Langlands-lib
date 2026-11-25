/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import WeilConjectures.AlgebraicGeometry.ContinuousLisseStratifiedLattices
import Mathlib.Algebra.Field.ULift
-- Internal transport lemmas are shared with `ContinuousConstructibleIntegralStratum` through a
-- private import.
set_option linter.privateModule false

/-! # Integral models on a locally finitely presented stratum

Source: Bhatt--Scholze, Lemmas 6.8.12--6.8.13 and Proposition 6.8.14(2).
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private lemma constructible_comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj T] (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) T}
    (h : ProEtale.IsConstructibleModuleObject T M) :
    ProEtale.IsConstructibleModuleObject R ((Mod.comap φ).obj M) := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun a ↦ ?_⟩
  let G := ProEtale.upperStar Ab.{u + 1} (S.immersion a)
  obtain ⟨C, hC⟩ := ProEtale.lfp_comap (G.map φ) (hS a)
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨n, m, f, ⟨e⟩⟩ := hC i
  exact ⟨n, m, f, ⟨(((ProEtale.upperStar Ab.{u + 1} (C.f i)).mapMod _).mapIso
    ((G.mapModComapIso φ).app M)) ≪≫ e⟩⟩

private noncomputable def scalarTransportIso {X : Scheme.{u}}
    {R S R' S' : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj R'] [MonObj S']
    [IsCommMonObj R] [IsCommMonObj R']
    (φ : R ⟶ S) [IsMonHom φ] (ψ : R' ⟶ S') [IsMonHom ψ]
    (a : R ⟶ R') [IsMonHom a] [IsIso a]
    (b : S ⟶ S') [IsMonHom b] [IsIso b]
    (w : a ≫ ψ = φ ≫ b) :
    Mod.comap a ⋙ Mod.extendScalars φ ≅ Mod.extendScalars ψ ⋙ Mod.comap b := by
  let ea : Mod _ R' ≌ Mod _ R :=
    CategoryTheory.Equivalence.mk (Mod.comap a) (Mod.comap (inv a))
      ((Mod.comapId R').symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapComp (inv a) a)
      ((Mod.comapComp a (inv a)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId R)
  let eb : Mod _ S' ≌ Mod _ S :=
    CategoryTheory.Equivalence.mk (Mod.comap b) (Mod.comap (inv b))
      ((Mod.comapId S').symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapComp (inv b) b)
      ((Mod.comapComp b (inv b)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId S)
  let t : Mod.comap φ ⋙ Mod.comap (inv a) ≅ Mod.comap (inv b) ⋙ Mod.comap ψ :=
    (Mod.comapComp (inv a) φ).symm ≪≫ Mod.comapCongr (by
      rw [← cancel_epi a, IsIso.hom_inv_id_assoc, ← Category.assoc, w,
        Category.assoc, IsIso.hom_inv_id, Category.comp_id]) ≪≫ Mod.comapComp ψ (inv b)
  exact (ea.toAdjunction.comp (Mod.extendRestrictAdjunction φ)).leftAdjointUniq
    ((Mod.extendRestrictAdjunction ψ).comp eb.toAdjunction |>.ofNatIsoRight t.symm)

private lemma model_transport {X : Scheme.{u}}
    {R S R' S' : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj R'] [MonObj S']
    [IsCommMonObj R] [IsCommMonObj R']
    (φ : R ⟶ S) [IsMonHom φ] (ψ : R' ⟶ S') [IsMonHom ψ]
    (a : R ⟶ R') [IsMonHom a] [IsIso a]
    (b : S ⟶ S') [IsMonHom b] [IsIso b]
    (w : a ≫ ψ = φ ≫ b)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R')
    (hM : ProEtale.IsConstructibleModuleObject R' M)
    (e : (Mod.extendScalars ψ).obj M ≅ (Mod.comap (inv b)).obj F) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R,
      ProEtale.IsConstructibleModuleObject R N ∧
      Nonempty ((Mod.extendScalars φ).obj N ≅ F) := by
  refine ⟨(Mod.comap a).obj M, constructible_comap a hM, ⟨?_⟩⟩
  exact (scalarTransportIso φ ψ a b w).app M ≪≫ (Mod.comap b).mapIso e ≪≫
    ((Mod.comapComp b (inv b)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId S).app F

private noncomputable def liftCoefficientIso (E : Type) [NormedField E] :
    Profinite.continuousMapRingSheaf.{u} E ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} E) where
  hom := ⟨
    { app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((ULift.ringEquiv (R := E)).symm.toRingHom.compLeftContinuous S.unop
            continuous_uliftUp).comp ULift.ringEquiv.toRingHom))
      naturality := fun _ _ _ ↦ rfl }⟩
  inv := ⟨
    { app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((ULift.ringEquiv (R := E)).toRingHom.compLeftContinuous S.unop
            continuous_uliftDown).comp ULift.ringEquiv.toRingHom))
      naturality := fun _ _ _ ↦ rfl }⟩
  hom_inv_id := by ext S f; rfl
  inv_hom_id := by ext S f; rfl

private lemma smallField_finiteFree_cover
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : ProEtale.IsLocallyFinitelyPresented
      (condensedRingObj (Profinite.continuousMapRingObj E) X) P) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      Mod.IsFree
        ((ProEtale.upperStar Ab.{u + 1} (C.f i)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (C.f i)).mapMod
          (condensedRingObj (Profinite.continuousMapRingObj E) X)).obj P) := by
  let : NormedField (ULift.{u} E) :=
    { (inferInstance : Field (ULift.{u} E)), (inferInstance : NormedCommRing (ULift.{u} E)) with
      dist_eq x y := dist_eq_norm_neg_add x.down y.down
      norm_mul x y := norm_mul x.down y.down }
  let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E) :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E)).symm.finiteDimensional
  let e := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (liftCoefficientIso E)
  have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map _ (liftCoefficientIso E).hom
  let φ := (upperStarFromPoint X).map e.hom
  have : IsMonHom φ := inferInstance
  let Q := (Mod.comap (inv φ)).obj P
  have hQ := ProEtale.lfp_comap (inv φ) hP
  obtain ⟨C, hC⟩ := ProEtale.exists_finiteFree_cover_of_condensedField_lfp ℓ
    (ULift.{u} E) X Q hQ
  refine ⟨C, fun i ↦ ?_⟩
  let G := ProEtale.upperStar Ab.{u + 1} (C.f i)
  have h := ProEtale.free_comap (G.map φ) (hC i)
  obtain ⟨n, ⟨e⟩⟩ := h
  refine ⟨n, ⟨?_ ≪≫ e⟩⟩
  exact (G.mapMod _).mapIso
    (((Mod.comapComp φ (inv φ)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId _).app P).symm ≪≫
      (G.mapModComapIso φ).app Q

private structure PullbackCoefficientDataCore
    (Λ₀ Λ₁ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    (φ : Λ₀ ⟶ Λ₁) [IsMonHom φ]
    {X Y : Scheme.{u}} (i : Y ⟶ X) where
  integral : (ProEtale.upperStar Ab.{u + 1} i).obj
      (condensedRingObj Λ₀ X) ⟶ condensedRingObj Λ₀ Y
  rational : (ProEtale.upperStar Ab.{u + 1} i).obj
      (condensedRingObj Λ₁ X) ⟶
        condensedRingObj Λ₁ Y
  integralMon : IsMonHom integral
  rationalMon : IsMonHom rational
  integralIso : IsIso integral
  rationalIso : IsIso rational
  square : integral ≫ coefficientMap φ Y =
    (ProEtale.upperStar Ab.{u + 1} i).map (coefficientMap φ X) ≫
      rational
  pullback : letI := rationalMon
    letI := rationalIso
    CondensedRing.upperStar Λ₁ i ≅
    (ProEtale.upperStar Ab.{u + 1} i).mapMod _ ⋙ Mod.comap (inv rational)

private noncomputable def pullbackCoefficientDataCore
    (Λ₀ Λ₁ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    (φ : Λ₀ ⟶ Λ₁) [IsMonHom φ]
    {X Y : Scheme.{u}} (i : Y ⟶ X) : PullbackCoefficientDataCore Λ₀ Λ₁ φ i where
  integral := condensedPullbackHom Λ₀ i
  rational := condensedPullbackHom Λ₁ i
  integralMon := ProEtale.isMonHom_condensedPullbackHom _ _
  rationalMon := ProEtale.isMonHom_condensedPullbackHom _ _
  integralIso := ProEtale.isIso_condensedPullbackHom _ _
  rationalIso := ProEtale.isIso_condensedPullbackHom _ _
  square := (map_coefficientMap_comp_condensedPullbackHom φ i).symm
  pullback := Functor.isoWhiskerLeft _ (Mod.extendScalarsIsoComapInv _)

private abbrev PullbackCoefficientData
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (i : Y ⟶ X) :=
  PullbackCoefficientDataCore (integralCoeff ℓ E) (Profinite.continuousMapRingObj E)
    (integralScalarMap ℓ E) i

private noncomputable def pullbackCoefficientData
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (i : Y ⟶ X) : PullbackCoefficientData ℓ E i :=
  pullbackCoefficientDataCore (integralCoeff ℓ E) (Profinite.continuousMapRingObj E)
    (integralScalarMap ℓ E) i

private theorem pullbackCoefficient_model
    (Λ₀ Λ₁ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    (φ : Λ₀ ⟶ Λ₁) [IsMonHom φ]
    {X Y : Scheme.{u}} (i : Y ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₁ X))
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ₀ Y))
    (hM : ProEtale.IsConstructibleModuleObject (condensedRingObj Λ₀ Y) M)
    (e : (Mod.extendScalars (coefficientMap φ Y)).obj M ≅
      (CondensedRing.upperStar Λ₁ i).obj P) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        ((ProEtale.upperStar Ab.{u + 1} i).obj (condensedRingObj Λ₀ X)),
      ProEtale.IsConstructibleModuleObject
        ((ProEtale.upperStar Ab.{u + 1} i).obj (condensedRingObj Λ₀ X)) N ∧
      Nonempty ((Mod.extendScalars
        ((ProEtale.upperStar Ab.{u + 1} i).map (coefficientMap φ X))).obj N ≅
        ((ProEtale.upperStar Ab.{u + 1} i).mapMod _).obj P) := by
  obtain ⟨D⟩ : Nonempty (PullbackCoefficientDataCore Λ₀ Λ₁ φ i) :=
    ⟨pullbackCoefficientDataCore Λ₀ Λ₁ φ i⟩
  obtain ⟨a, b, ha, hb, ia, ib, w, t⟩ := D
  let : IsMonHom a := ha
  let : IsMonHom b := hb
  let : IsIso a := ia
  let : IsIso b := ib
  let G := ProEtale.upperStar Ab.{u + 1} i
  exact model_transport (X := Y)
    (R := G.obj (condensedRingObj Λ₀ X)) (S := G.obj (condensedRingObj Λ₁ X))
    (R' := condensedRingObj Λ₀ Y) (S' := condensedRingObj Λ₁ Y)
    (G.map (coefficientMap φ X)) (coefficientMap φ Y)
    a b w ((G.mapMod _).obj P) M hM (e ≪≫ t.app P)

end AlgebraicGeometry.ProEtale.CondensedRing
