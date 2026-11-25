/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Comparing the actual diagonal scalar functor with small-site coefficients

Source: Stacks Tags 00YY, 03CY and 093M; the diagonal tower limit, clause (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v a b va vb
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

private local instance coefficientDown_equivalence (S : Scheme.{u}) :
    (AsSmall.down : Scheme.proEtaleSiteModel S ⥤ S.ProEt).IsEquivalence :=
  inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt)).inverse.IsEquivalence)

private local instance coefficientDown_dense (S : Scheme.{u}) :
    (AsSmall.down : Scheme.proEtaleSiteModel S ⥤ S.ProEt).IsDenseSubsite
      (Scheme.proEtaleModelTopology S) (Scheme.ProEt.topology S) := by
  change (AsSmall.down : Scheme.proEtaleSiteModel S ⥤ S.ProEt).IsDenseSubsite
    ((AsSmall.down : Scheme.proEtaleSiteModel S ⥤ S.ProEt).inducedTopology
      (Scheme.ProEt.topology S)) (Scheme.ProEt.topology S)
  infer_instance

private local instance coefficientDown_cocontinuous (S : Scheme.{u}) :
    (AsSmall.down : Scheme.proEtaleSiteModel S ⥤ S.ProEt).IsCocontinuous
      (Scheme.proEtaleModelTopology S) (Scheme.ProEt.topology S) := by
  let := coefficientDown_dense S
  infer_instance

private abbrev coefficientModelRings (S : Scheme.{u}) :=
  (AsSmall.down : Scheme.proEtaleSiteModel S ⥤ S.ProEt).sheafPushforwardContinuous
    CommRingCat.{u + 1} (Scheme.proEtaleModelTopology S) (Scheme.ProEt.topology S)

private def coefficientQuotientTower (S : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] (I : Ideal A) : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology S) CommRingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n ↦
    (constantSheaf (Scheme.ProEt.topology S) CommRingCat.{u + 1}).obj
      (CommRingCat.of (A ⧸ I ^ (n + 1)))) (fun n ↦
        (constantSheaf (Scheme.ProEt.topology S) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1))))

private def coefficientModelConstantsIso (S : Scheme.{u}) :
    constantSheaf (Scheme.ProEt.topology S) CommRingCat.{u + 1} ⋙
      coefficientModelRings S ≅
      constantSheaf (Scheme.proEtaleModelTopology S) CommRingCat.{u + 1} :=
  NatIso.ofComponents (fun A ↦
    ((AsSmall.down : Scheme.proEtaleSiteModel S ⥤
      S.ProEt).pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
        (Scheme.proEtaleModelTopology S) (Scheme.ProEt.topology S)).symm.app
          ((Functor.const S.ProEtᵒᵖ).obj A)) (by
    intro A B f
    exact ((AsSmall.down : Scheme.proEtaleSiteModel S ⥤
      S.ProEt).pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
        (Scheme.proEtaleModelTopology S) (Scheme.ProEt.topology S)).inv.naturality
          ((Functor.const S.ProEtᵒᵖ).map f))

attribute [local irreducible] coefficientModelConstantsIso

private def coefficientModelSystemIso (S : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] (I : Ideal A) :
    coefficientQuotientTower S I ⋙ coefficientModelRings S ≅
      ConstantCompletion.finiteSystem (Scheme.proEtaleModelTopology S) A I := by
  refine NatIso.ofComponents (fun n ↦ (coefficientModelConstantsIso S).app
    (CommRingCat.of (A ⧸ I ^ (n.unop + 1)))) ?_
  intro n m f
  let hn := NatTrans.ofOpSequence
    (F := coefficientQuotientTower S I ⋙ coefficientModelRings S)
    (G := ConstantCompletion.finiteSystem (Scheme.proEtaleModelTopology S) A I)
    (fun n ↦ (coefficientModelConstantsIso S).hom.app
      (CommRingCat.of (A ⧸ I ^ (n + 1)))) (by
      intro n
      simpa only [Functor.comp_map, coefficientQuotientTower,
        ConstantCompletion.finiteSystem, Functor.ofOpSequence_map_homOfLE_succ,
        ConstantCompletion.transition] using (coefficientModelConstantsIso S).hom.naturality
        (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1))))
  exact hn.naturality f

attribute [local irreducible] coefficientModelSystemIso

private def coefficientModelCompletionIso (S : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] (I : Ideal A) :
    (coefficientModelRings S).obj (limit (coefficientQuotientTower S I)) ≅
      ConstantCompletion.completed (Scheme.proEtaleModelTopology S) A I :=
  preservesLimitIso (coefficientModelRings S) (coefficientQuotientTower S I) ≪≫
    lim.mapIso (coefficientModelSystemIso S I)

attribute [local irreducible] coefficientModelCompletionIso

private theorem coefficientModelCompletionIso_projection (S : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] (I : Ideal A) (n : ℕ) :
    (coefficientModelCompletionIso S I).hom ≫
        ConstantCompletion.projection (Scheme.proEtaleModelTopology S) A I n =
      (coefficientModelRings S).map (limit.π (coefficientQuotientTower S I) (op n)) ≫
        (coefficientModelConstantsIso S).hom.app (CommRingCat.of (A ⧸ I ^ (n + 1))) := by
  unfold coefficientModelCompletionIso
  change ((preservesLimitIso (coefficientModelRings S) (coefficientQuotientTower S I)).hom ≫
    lim.map (coefficientModelSystemIso S I).hom) ≫ _ = _
  erw [Category.assoc, limMap_π, ← Category.assoc, preservesLimitIso_hom_π]
  unfold coefficientModelSystemIso
  rfl

private theorem coefficientRestrictionExact
    {C : Type a} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{b}] [J.WEqualsLocallyBijective AddCommGrpCat.{b}]
    {R S : Sheaf J RingCat.{b}} (r : R ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{b} r) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{b} r) := by
  let F := SheafOfModules.restrictScalars.{b} r
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{b} R) :=
    (moduleSheaves_colimits_forgetful R).2.2.1
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{b} S) :=
    (moduleSheaves_colimits_forgetful S).2.2.1
  have : PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf.{b} R) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{b} S))
  have : PreservesFiniteColimits (F ⋙ SheafOfModules.toSheaf.{b} R) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{b} S))
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{b} R) := inferInstance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{b} R),
    preservesFiniteColimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{b} R)⟩

private def finiteIso (l : ℕ) [Fact l.Prime] (n : ℕ) :
    (ULift.{u + 1} ℤ_[l] ⧸ (Ideal.span {(l : ULift.{u + 1} ℤ_[l])}) ^ (n + 1)) ≃+*
      ULift.{u + 1} (ZMod (l ^ (n + 1))) :=
  (Ideal.quotientEquiv _ _ ULift.ringEquiv (by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    rfl)).trans
    ((Ideal.quotEquivOfEq ((Ideal.span_singleton_pow _ _).trans
      (PadicInt.ker_toZModPow (n + 1)).symm)).trans
      ((RingHom.quotientKerEquivOfSurjective
        (ZMod.ringHom_surjective (PadicInt.toZModPow (n + 1)))).trans
          ULift.ringEquiv.symm))

private def finiteTowerIso (l : ℕ) [Fact l.Prime] (S : Scheme.{u}) :
    coefficientQuotientTower S (Ideal.span {(l : ULift.{u + 1} ℤ_[l])}) ≅
      Scheme.purTwistZlTower S l := by
  let e (n : ℕ) := (constantSheaf (Scheme.ProEt.topology S) CommRingCat.{u + 1}).mapIso
    (finiteIso l n).toCommRingCatIso
  let t : coefficientQuotientTower S (Ideal.span {(l : ULift.{u + 1} ℤ_[l])}) ⟶
      Scheme.purTwistZlTower S l := NatTrans.ofOpSequence (fun n ↦ (e n).hom) (by
    intro n
    simp only [coefficientQuotientTower, Scheme.purTwistZlTower,
      Scheme.purTwistZlTowerOfUniverses, Functor.ofOpSequence_map_homOfLE_succ]
    dsimp only [e, Scheme.purTwistFiniteTransition, Scheme.purTwistFiniteTransitionOfUniverses,
      Functor.mapIso_hom]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext x
    change PadicInt.toZModPow (n + 1) x.down =
      (ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
        (ZMod (l ^ (n + 1)))) (PadicInt.toZModPow (n + 2) x.down)
    exact (RingHom.congr_fun
      (PadicInt.zmod_cast_comp_toZModPow (n + 1) (n + 2) (Nat.le_succ _)) x.down).symm)
  have : ∀ n, IsIso (t.app n) := fun n ↦ inferInstanceAs (IsIso (e n.unop).hom)
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

private noncomputable def moduleSiteEquivalence
    {C : Type*} [Category C] {H : Type*} [Category H]
    (J : GrothendieckTopology C) (K : GrothendieckTopology H)
    (e : C ≌ H) [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
    (R : Sheaf J RingCat.{v}) (S : Sheaf K RingCat.{v})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{v} K J).obj R) :
    SheafOfModules.{v} R ≌ SheafOfModules.{v} S := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{v} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    rw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    rw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    rw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      simp
    rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  exact SheafOfModules.pushforwardPushforwardEquivalence e.symm c.hom ψ H₁ H₂

private def ringModuleEquiv {C : Type a} [Category.{va} C]
    {J : GrothendieckTopology C} {R B : Sheaf J RingCat.{v}} (e : R ≅ B) :
    SheafOfModules.{v} B ≌ SheafOfModules.{v} R := by
  let : (CategoryTheory.Equivalence.refl (C := C)).functor.IsContinuous J J :=
    inferInstanceAs ((𝟭 C).IsContinuous J J)
  let : (CategoryTheory.Equivalence.refl (C := C)).inverse.IsContinuous J J :=
    inferInstanceAs ((𝟭 C).IsContinuous J J)
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (CategoryTheory.Equivalence.refl (C := C)) e.hom e.inv
    (by
      apply NatTrans.ext
      funext U
      change B.obj.map (𝟙 U) = e.inv.hom.app U ≫ e.hom.hom.app U
      rw [CategoryTheory.Functor.map_id]
      exact congrArg (fun f : B ⟶ B ↦ f.hom.app U) e.inv_hom_id.symm)
    (by
      apply NatTrans.ext
      funext U
      change e.hom.hom.app U ≫ e.inv.hom.app U ≫ R.obj.map (𝟙 U) = 𝟙 _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact congrArg (fun f : R ⟶ R ↦ f.hom.app U) e.hom_inv_id)

private def completedRingIso (l : ℕ) [Fact l.Prime] (S : Scheme.{u}) :
    ConstantCompletion.completed (Scheme.proEtaleModelTopology S) (ULift.{u + 1} ℤ_[l])
        (Ideal.span {(l : ULift.{u + 1} ℤ_[l])}) ≅
      (coefficientModelRings S).obj (Scheme.purTwistZlCompletion S l) :=
  (coefficientModelCompletionIso S (Ideal.span {(l : ULift.{u + 1} ℤ_[l])})).symm ≪≫
    (coefficientModelRings S).mapIso (lim.mapIso (finiteTowerIso l S))

private theorem completedRingIso_projection (l : ℕ) [Fact l.Prime] (S : Scheme.{u}) (n : ℕ) :
    (completedRingIso l S).hom ≫
        (coefficientModelRings S).map (Scheme.purTwistZlProjection S l n) =
      ConstantCompletion.projection (Scheme.proEtaleModelTopology S) (ULift.{u + 1} ℤ_[l])
          (Ideal.span {(l : ULift.{u + 1} ℤ_[l])}) n ≫
        (coefficientModelConstantsIso S).inv.app
          (CommRingCat.of (ULift.{u + 1} ℤ_[l] ⧸
            (Ideal.span {(l : ULift.{u + 1} ℤ_[l])}) ^ (n + 1))) ≫
        (coefficientModelRings S).map
          ((constantSheaf (Scheme.ProEt.topology S) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom (finiteIso l n).toRingHom)) := by
  dsimp only [completedRingIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp]
  change _ ≫ (coefficientModelRings S).map
    (limMap (finiteTowerIso l S).hom ≫ limit.π (Scheme.purTwistZlTower S l) (op n)) = _
  rw [limMap_π, Functor.map_comp, ← Category.assoc]
  have ht : (finiteTowerIso l S).hom.app (op n) =
      (constantSheaf (Scheme.ProEt.topology S) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (finiteIso l n).toRingHom) := rfl
  rw [ht, ← Category.assoc]
  congr 1
  apply (cancel_mono ((coefficientModelConstantsIso S).hom.app _)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← coefficientModelCompletionIso_projection]
  simp only [Iso.symm_hom, Iso.inv_hom_id_assoc]

private theorem completedRingIso_map (l : ℕ) [Fact l.Prime] (S : Scheme.{u}) :
    ConstantCompletion.coefficientMap (Scheme.proEtaleModelTopology S) (ULift.{u + 1} ℤ_[l])
        (Ideal.span {(l : ULift.{u + 1} ℤ_[l])}) ≫ (completedRingIso l S).hom =
      (coefficientModelConstantsIso S).inv.app (CommRingCat.of (ULift.{u + 1} ℤ_[l])) ≫
        (coefficientModelRings S).map (Scheme.purTwistZlCompletionMap S l) := by
  apply (isLimitOfPreserves (coefficientModelRings S)
    (limit.isLimit (Scheme.purTwistZlTower S l))).hom_ext
  intro n
  change _ ≫ (coefficientModelRings S).map (Scheme.purTwistZlProjection S l n.unop) =
    _ ≫ (coefficientModelRings S).map (Scheme.purTwistZlProjection S l n.unop)
  rw [Category.assoc, completedRingIso_projection]
  simp only [← Category.assoc]
  rw [ConstantCompletion.coefficientMap, ConstantCompletion.projection, limit.lift_π]
  change ((constantSheaf (Scheme.proEtaleModelTopology S) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk
        ((Ideal.span {(l : ULift.{u + 1} ℤ_[l])}) ^ (n.unop + 1)))) ≫ _) ≫ _ = _
  rw [(coefficientModelConstantsIso S).inv.naturality]
  simp only [Functor.comp_map, Category.assoc]
  apply (cancel_epi ((coefficientModelConstantsIso S).inv.app
    (CommRingCat.of (ULift.{u + 1} ℤ_[l])))).mpr
  rw [← (coefficientModelRings S).map_comp, ← (coefficientModelRings S).map_comp]
  apply congrArg (coefficientModelRings S).map
  have h := (Scheme.purTwistZlCompletionMap_existsUnique S l).exists.choose_spec n.unop
  change Scheme.purTwistZlCompletionMap S l ≫ Scheme.purTwistZlProjection S l n.unop =
    Scheme.purTwistZlReduction S l n.unop at h
  rw [h, ← Functor.map_comp]
  apply congrArg (constantSheaf (Scheme.ProEt.topology S) CommRingCat.{u + 1}).map
  apply CommRingCat.hom_ext
  ext x
  rfl

private def restrictionTransport
    {C : Type a} [Category.{va} C] {D : Type b} [Category.{vb} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
    {R B : Sheaf J RingCat.{v}} {R' B' : Sheaf K RingCat.{v}}
    (cR : R' ≅ (e.inverse.sheafPushforwardContinuous RingCat.{v} K J).obj R)
    (cB : B' ≅ (e.inverse.sheafPushforwardContinuous RingCat.{v} K J).obj B)
    (φ : R ⟶ B) (φ' : R' ⟶ B')
    (hφ : φ' ≫ cB.hom = cR.hom ≫
      (e.inverse.sheafPushforwardContinuous RingCat.{v} K J).map φ) :
    SheafOfModules.restrictScalars.{v} φ ⋙ (moduleSiteEquivalence J K e R R' cR).functor ≅
      (moduleSiteEquivalence J K e B B' cB).functor ⋙
        SheafOfModules.restrictScalars.{v} φ' := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ ?_) ?_)
    · refine ModuleCat.isoMk (Iso.refl _) ?_
      intro r
      ext x
      have h := congrArg (fun f ↦ f.hom.app U r) hφ
      exact congrArg (fun z : B.obj.obj (e.inverse.op.obj U) ↦
        @SMul.smul (B.obj.obj (e.inverse.op.obj U)) (M.val.obj (e.inverse.op.obj U))
          inferInstance z x) h
    · intro U V g
      ext x
      rfl
  · intro M N g
    ext U x
    rfl

attribute [local irreducible] moduleSiteEquivalence completedRingIso finiteTowerIso

/-- The small-site and constant-ring encodings identify the actual scalar functor,
including its action on all derived morphisms. No completeness assertion occurs here.

Source: Stacks Tags 00YY, 03CY and 093M; blueprint diagonal tower limit, clause (3).
(blueprint: lem-sfb-diagonal-completion-coefficient-transport-core).

Proof: precompose sheaves with the canonical AsSmall equivalence of the pro-etale site.
This gives exact equivalences for both coefficient categories. The constant-ring
module equivalence identifies constant Z_l-module sheaves with modules over the
constant ring sheaf. For each positive exponent m, the surjective residue map
Z_l to Z/l^m has kernel (l^m), so it induces the quotient ring isomorphism
Z_l/(l^m) = Z/l^m. Lift the ring isomorphisms to the coefficient universe and
apply constant sheafification. The residue-map equations identify every transition.
The universal property of limits gives the completed-ring isomorphism, and its
projection equations identify the actual constant-to-completed coefficient map.
Restriction along this ring isomorphism, combined with the site equivalences,
gives the completed-category equivalence. On the abelian categories the restriction
square is the identity on underlying sections, hence a natural isomorphism.
Exact-functor localization transports the square and both equivalences through
arbitrary choices of derived localization. Exactness also makes both directions
of the constant-category equivalence additive. -/
theorem diagonalCompletionCoefficientTransportCore (l : ℕ) [Fact l.Prime] (S : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalMod l S)]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted l S)] :
    let J := Scheme.proEtaleModelTopology S
    let A := ULift.{u + 1} ℤ_[l]
    let I : Ideal A := Ideal.span {(l : A)}
    ∃ (EB : DerivedCategory (DiagonalCompleted l S) ≌
          ConstantCompletion.D (ConstantCompletion.completed J A I))
      (ER : DerivedCategory (DiagonalMod l S) ≌
          ConstantCompletion.D (ConstantCompletion.constant J A)),
      ER.functor.Additive ∧ ER.inverse.Additive ∧
      Nonempty (diagonalCompletedUnderlying l S ⋙ ER.functor ≅
        EB.functor ⋙ ConstantCompletion.dres (ConstantCompletion.coefficientMap J A I)) := by
  let J₀ := Scheme.ProEt.topology S
  let J := Scheme.proEtaleModelTopology S
  let A := ULift.{u + 1} ℤ_[l]
  let I : Ideal A := Ideal.span {(l : A)}
  let R₀ := Scheme.purTwistZlConstant S l
  let B₀ := Scheme.purTwistZlCompletion S l
  let R := ConstantCompletion.constant J A
  let B := ConstantCompletion.completed J A I
  let φ₀ := Scheme.purTwistZlCompletionMap S l
  let φ := ConstantCompletion.coefficientMap J A I
  let e : S.ProEt ≌ Scheme.proEtaleSiteModel S := AsSmall.equiv.{u, u + 1, u + 1}
  let : e.functor.IsContinuous J₀ J := Scheme.proEtaleModelUp_isContinuous S
  let : e.inverse.IsContinuous J J₀ := inferInstanceAs
    ((AsSmall.down : Scheme.proEtaleSiteModel S ⥤ S.ProEt).IsContinuous
      (Scheme.proEtaleModelTopology S) (Scheme.ProEt.topology S))
  let f₀ := sheafCompose J₀ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let f := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let cR : f.obj R ≅
      (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} J J₀).obj (f₀.obj R₀) :=
    f.mapIso ((coefficientModelConstantsIso S).app (CommRingCat.of A)).symm
  let cB : f.obj B ≅
      (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} J J₀).obj (f₀.obj B₀) :=
    f.mapIso (completedRingIso l S)
  have hc : f.map φ ≫ cB.hom = cR.hom ≫
      (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} J J₀).map (f₀.map φ₀) := by
    have h := congrArg f.map (completedRingIso_map l S)
    simp only [Functor.map_comp] at h
    convert h using 1 <;> rfl
  let EB₀ := moduleSiteEquivalence J₀ J e (f₀.obj B₀) (f.obj B) cB
  let ER₀ := moduleSiteEquivalence J₀ J e (f₀.obj R₀) (f.obj R) cR
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1} (f₀.obj R₀))
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := HasDerivedCategory.standard (ConstantCompletion.Mod B)
  let : EB₀.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : EB₀.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let : ER₀.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : ER₀.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let := Scheme.purTwistForgetPreservesSheafification S
  obtain ⟨q, hq, _, _, _⟩ := (constant_ring_module_sheaves J₀ A).1
  let r := ringModuleEquiv ((constantCommuteCompose J₀
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of A)).symm
  let E₀ := r.trans q
  let ER := E₀.symm.trans ER₀
  let : E₀.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : E₀.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let : ER.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : ER.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let T₀ := SheafOfModules.restrictScalars.{u + 1} (f₀.map φ₀)
  let T := ConstantCompletion.res φ
  let := (coefficientRestrictionExact (f₀.map φ₀)).1
  let := (coefficientRestrictionExact (f₀.map φ₀)).2
  let := (siteRestrictScalars_exact φ).1
  let := (siteRestrictScalars_exact φ).2
  have hF : diagonalCompletedRestriction l S = T₀ ⋙ E₀.functor := by
    change diagonalCompletedRestriction l S = T₀ ⋙ (r.functor ⋙ q.functor)
    rw [hq]
    rfl
  let α₀ : diagonalCompletedRestriction l S ⋙ ER.functor ≅ EB₀.functor ⋙ T := by
    rw [hF]
    exact Functor.isoWhiskerLeft T₀
      (Functor.isoWhiskerRight E₀.unitIso.symm ER₀.functor) ≪≫
        restrictionTransport J₀ J e cR cB (f₀.map φ₀) (f.map φ) hc
  refine ⟨EB₀.mapDerivedCategory, ER.mapDerivedCategory,
    Functor.additive_of_preserves_binary_products _,
    Functor.additive_of_preserves_binary_products _, ⟨?_⟩⟩
  exact Functor.mapDerivedCategoryCompIso (diagonalCompletedRestriction l S)
      ER.functor ≪≫
    Functor.mapDerivedCategoryNatIso α₀ ≪≫
    (Functor.mapDerivedCategoryCompIso EB₀.functor T).symm

end AlgebraicGeometry.ProEtale.DiagonalTrace
