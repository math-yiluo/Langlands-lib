/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-! # Flatness and quotients of a completed constant algebra

Source: Stacks Project, Modules on Sites, Tag 093M (lemma-completion-flat).
The coefficient presentation is allowed to change by specified ring isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open AdicCoefficients
open scoped ChangeOfRings

namespace CompletedConstantAlgebra

private abbrev smallSite (T : Scheme.{u}) := AsSmall.{u + 1} T.ProEt
private abbrev smallTopology (T : Scheme.{u}) :=
  (AsSmall.down : smallSite T ⥤ T.ProEt).inducedTopology (ProEt.topology T)
private instance down_isEquivalence (T : Scheme.{u}) :
    (AsSmall.down : smallSite T ⥤ T.ProEt).IsEquivalence :=
  inferInstanceAs ((AsSmall.equiv (C := T.ProEt)).inverse.IsEquivalence)
private instance down_isDenseSubsite (T : Scheme.{u}) :
    (AsSmall.down : smallSite T ⥤ T.ProEt).IsDenseSubsite
      (smallTopology T) (ProEt.topology T) := by
  change (AsSmall.down : smallSite T ⥤ T.ProEt).IsDenseSubsite
    ((AsSmall.down : smallSite T ⥤ T.ProEt).inducedTopology (ProEt.topology T))
    (ProEt.topology T)
  infer_instance
private noncomputable def constantsIso (T : Scheme.{u}) :
    constantSheaf (ProEt.topology T) CommRingCat.{u + 1} ⋙
      (AsSmall.down : smallSite T ⥤ T.ProEt).sheafPushforwardContinuous
        CommRingCat.{u + 1} (smallTopology T) (ProEt.topology T) ≅
      constantSheaf (smallTopology T) CommRingCat.{u + 1} :=
  NatIso.ofComponents (fun A ↦
    ((AsSmall.down : smallSite T ⥤ T.ProEt).pushforwardContinuousSheafificationCompatibility
        CommRingCat.{u + 1} (smallTopology T) (ProEt.topology T)).symm.app
          ((Functor.const T.ProEtᵒᵖ).obj A)) (by
    intro A B f
    exact ((AsSmall.down : smallSite T ⥤ T.ProEt).pushforwardContinuousSheafificationCompatibility
        CommRingCat.{u + 1} (smallTopology T) (ProEt.topology T)).inv.naturality
          ((Functor.const T.ProEtᵒᵖ).map f))

attribute [local irreducible] constantsIso

private abbrev pushRing (T : Scheme.{u}) :=
  (AsSmall.down : smallSite T ⥤ T.ProEt).sheafPushforwardContinuous
    CommRingCat.{u + 1} (smallTopology T) (ProEt.topology T)
private noncomputable def systemIso (T : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] (I : Ideal A) :
    adicLisseRingSystem T I ⋙ pushRing T ≅
      ConstantCompletion.finiteSystem (smallTopology T) A I := by
  refine NatIso.ofComponents (fun n ↦ (constantsIso T).app
    (CommRingCat.of (A ⧸ I ^ (n.unop + 1)))) ?_
  intro n m f
  change (pushRing T).map ((adicLisseRingSystem T I).map f) ≫ _ = _
  let hn := (NatTrans.ofOpSequence
    (F := adicLisseRingSystem T I ⋙ pushRing T)
    (G := ConstantCompletion.finiteSystem (smallTopology T) A I) (fun n ↦
    (constantsIso T).hom.app (CommRingCat.of (A ⧸ I ^ (n + 1)) )) (by
      intro n
      simpa only [Functor.comp_map, adicLisseRingSystem,
        ConstantCompletion.finiteSystem, Functor.ofOpSequence_map_homOfLE_succ,
        ConstantCompletion.transition] using (constantsIso T).hom.naturality
        (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1)))))
  exact hn.naturality f
attribute [local irreducible] systemIso

private noncomputable def completionIso (T : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] (I : Ideal A) :
    (pushRing T).obj (adicLisseCompletedRing T I) ≅
      ConstantCompletion.completed (smallTopology T) A I :=
  preservesLimitIso (pushRing T) (adicLisseRingSystem T I) ≪≫
    lim.mapIso (systemIso T I)

attribute [local irreducible] completionIso

private theorem completionIso_projection (T : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] (I : Ideal A) (n : ℕ) :
    (completionIso T I).hom ≫ ConstantCompletion.projection (smallTopology T) A I n =
      (pushRing T).map (limit.π (adicLisseRingSystem T I) (op n)) ≫
        (constantsIso T).hom.app (CommRingCat.of (A ⧸ I ^ (n + 1))) := by
  unfold completionIso
  change ((preservesLimitIso (pushRing T) (adicLisseRingSystem T I)).hom ≫
    lim.map (systemIso T I).hom) ≫ _ = _
  erw [Category.assoc, limMap_π, ← Category.assoc, preservesLimitIso_hom_π]
  unfold systemIso
  rfl

private theorem coefficientMap_eq (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (c : adicLisseConstantRing T A ⟶ adicLisseCompletedRing T I)
    (hc : ∀ n : ℕ, c ≫ limit.π (adicLisseRingSystem T I) (op n) =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) :
    (pushRing T).map c ≫ (completionIso T I).hom =
      (constantsIso T).hom.app (CommRingCat.of A) ≫
        ConstantCompletion.coefficientMap (smallTopology T) A I := by
  apply limit.hom_ext
  intro n
  change ((pushRing T).map c ≫ (completionIso T I).hom) ≫
      ConstantCompletion.projection (smallTopology T) A I n.unop =
    ((constantsIso T).hom.app (CommRingCat.of A) ≫
      ConstantCompletion.coefficientMap (smallTopology T) A I) ≫
        ConstantCompletion.projection (smallTopology T) A I n.unop
  rw [Category.assoc, completionIso_projection]
  rw [← Category.assoc, ← Functor.map_comp, hc]
  rw [Category.assoc]
  change _ = (constantsIso T).hom.app (CommRingCat.of A) ≫
    limit.lift _ (ConstantCompletion.quotientCone (smallTopology T) A I) ≫ _
  erw [limit.lift_π]
  exact (constantsIso T).hom.naturality _

private noncomputable def algebraIso (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) {S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (e : adicLisseCompletedRing T I ≅ S) :
    (pushRing T).obj S ≅ ConstantCompletion.completed (smallTopology T) A I :=
  (pushRing T).mapIso e.symm ≪≫ completionIso T I

attribute [local irreducible] algebraIso

private theorem algebraIso_scalar (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) {S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (e : adicLisseCompletedRing T I ≅ S) (c : adicLisseConstantRing T A ⟶ S)
    (hc : ∀ n : ℕ, c ≫ e.inv ≫ limit.π (adicLisseRingSystem T I) (op n) =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) :
    (pushRing T).map c ≫ (algebraIso T I e).hom =
      (constantsIso T).hom.app (CommRingCat.of A) ≫
        ConstantCompletion.coefficientMap (smallTopology T) A I := by
  unfold algebraIso
  dsimp only [ Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Functor.map_comp]
  exact coefficientMap_eq T I (c ≫ e.inv) (fun n ↦ by rw [Category.assoc]; exact hc n)

private theorem constantsIso_unit (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (U : (smallSite T)ᵒᵖ) (a : A) :
    ((constantsIso T).hom.app (CommRingCat.of A)).hom.app U
        ((adicLisseConstantUnit T A).app (AsSmall.down.op.obj U) a) =
      (ConstantCompletion.constantSection (J := smallTopology T) a).val U := by
  have h := Functor.toSheafify_pullbackSheafificationCompatibility
    (AsSmall.down : smallSite T ⥤ T.ProEt) CommRingCat.{u + 1}
      (smallTopology T) (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))
  have h' := congrArg (fun k ↦ k.app U) h
  have h'' := ConcreteCategory.congr_hom h' a
  unfold constantsIso
  change ((AsSmall.down.pushforwardContinuousSheafificationCompatibility
    CommRingCat.{u + 1} (smallTopology T) (ProEt.topology T)).inv.app
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).hom.app U
        ((adicLisseConstantUnit T A).app (AsSmall.down.op.obj U) a) = _
  refine (congrArg (fun z ↦
    ((AsSmall.down.pushforwardContinuousSheafificationCompatibility
      CommRingCat.{u + 1} (smallTopology T) (ProEt.topology T)).inv.app
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).hom.app U z) h'').symm.trans ?_
  exact ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U)
    ((AsSmall.down.pushforwardContinuousSheafificationCompatibility
      CommRingCat.{u + 1} (smallTopology T) (ProEt.topology T)).app
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).hom_inv_id) _

private theorem projection_transport (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) {S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (e : adicLisseCompletedRing T I ≅ S) (n : ℕ)
    {H : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (d : adicLisseConstantRing T (A ⧸ I ^ (n + 1)) ≅ H)
    (p : S ⟶ H) (hp : p = e.inv ≫ limit.π (adicLisseRingSystem T I) (op n) ≫ d.hom) :
    (algebraIso T I e).hom ≫ ConstantCompletion.projection (smallTopology T) A I n =
      (pushRing T).map p ≫ (pushRing T).map d.inv ≫
        (constantsIso T).hom.app (CommRingCat.of (A ⧸ I ^ (n + 1))) := by
  unfold algebraIso
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [Category.assoc, completionIso_projection, ← Category.assoc, ← Functor.map_comp]
  rw [hp]
  have hd : (e.inv ≫ limit.π (adicLisseRingSystem T I) (op n) ≫ d.hom) ≫ d.inv =
      e.inv ≫ limit.π (adicLisseRingSystem T I) (op n) := by simp
  have hm := congrArg ((pushRing T).map) hd
  rw [Functor.map_comp] at hm
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫
    (constantsIso T).hom.app (CommRingCat.of (A ⧸ I ^ (n + 1)))) hm.symm

private theorem projection_surjective_and_kernel (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (e : adicLisseCompletedRing T I ≅ S) (c : adicLisseConstantRing T A ⟶ S)
    (hc : ∀ n : ℕ, c ≫ e.inv ≫ limit.π (adicLisseRingSystem T I) (op n) =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
    (n : ℕ) {H : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (d : adicLisseConstantRing T (A ⧸ I ^ (n + 1)) ≅ H) (p : S ⟶ H)
    (hp : p = e.inv ≫ limit.π (adicLisseRingSystem T I) (op n) ≫ d.hom)
    (U : T.ProEtᵒᵖ) :
    Function.Surjective (p.hom.app U) ∧
      ∀ (M : Type (u + 1)) [AddCommGroup M] [Module (S.obj.obj U) M]
        (f : S.obj.obj U →ₗ[S.obj.obj U] M),
        (∀ a : ↥(I ^ (n + 1)),
          f (c.hom.app U ((adicLisseConstantUnit T A).app U (a : A))) = 0) →
        ∀ b : S.obj.obj U, p.hom.app U b = 0 → f b = 0 := by
  classical
  let V : (smallSite T)ᵒᵖ := op (AsSmall.up.obj U.unop)
  let B := ConstantCompletion.completed (smallTopology T) A I
  let Q := ConstantCompletion.finite (smallTopology T) A I n
  let β := algebraIso T I e
  let δ := (pushRing T).mapIso d.symm ≪≫
    (constantsIso T).app (CommRingCat.of (A ⧸ I ^ (n + 1)))
  have hcomp := projection_transport T I e n d p hp
  have heq (b : S.obj.obj U) :
      (ConstantCompletion.projection (smallTopology T) A I n).hom.app V
          (β.hom.hom.app V b) = δ.hom.hom.app V (p.hom.app U b) :=
    congrArg (fun k ↦ k.hom.app V b) hcomp
  have hβ (b : S.obj.obj U) : β.inv.hom.app V (β.hom.hom.app V b) = b :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app V) β.hom_inv_id) b
  have hβ' (b : B.obj.obj V) : β.hom.hom.app V (β.inv.hom.app V b) = b :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app V) β.inv_hom_id) b
  have hδ (b : H.obj.obj U) : δ.inv.hom.app V (δ.hom.hom.app V b) = b :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app V) δ.hom_inv_id) b
  obtain ⟨hsurj, hker⟩ :=
    (ConstantCompletion.flat_and_quotients (smallTopology T) A I).2.1 n V.unop
  constructor
  · intro y
    obtain ⟨b, hb⟩ := hsurj (δ.hom.hom.app V y)
    refine ⟨β.inv.hom.app V b, ?_⟩
    have hh := heq (β.inv.hom.app V b)
    change (ConstantCompletion.projection (smallTopology T) A I n).hom.app V
      (β.hom.hom.app V (β.inv.hom.app V b)) =
        δ.hom.hom.app V (p.hom.app U (β.inv.hom.app V b)) at hh
    rw [hβ', hb] at hh
    exact (hδ _).symm.trans ((congrArg (δ.inv.hom.app V) hh).symm.trans (hδ _))
  · intro M _ _ f hf b hb
    have hz : β.hom.hom.app V b ∈ Ideal.span (Set.range
        (fun a : ↥(I ^ (n + 1)) ↦
          (ConstantCompletion.algebraSection
            (ConstantCompletion.coefficientMap (smallTopology T) A I) (a : A)).val V)) := by
      rw [← hker]
      change (ConstantCompletion.projection (smallTopology T) A I n).hom.app V
        (β.hom.hom.app V b) = 0
      rw [heq, hb, map_zero]
    have hz' : ∀ z ∈ Ideal.span (Set.range
        (fun a : ↥(I ^ (n + 1)) ↦
          (ConstantCompletion.algebraSection
            (ConstantCompletion.coefficientMap (smallTopology T) A I) (a : A)).val V)),
        f (β.inv.hom.app V z) = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a, rfl⟩ := hz
        have hh := congrArg (fun k ↦ k.hom.app V
          ((adicLisseConstantUnit T A).app U (a : A)))
            (algebraIso_scalar T I e c hc)
        change β.hom.hom.app V
            (c.hom.app U ((adicLisseConstantUnit T A).app U (a : A))) =
          (ConstantCompletion.coefficientMap (smallTopology T) A I).hom.app V
            (((constantsIso T).hom.app (CommRingCat.of A)).hom.app V
              ((adicLisseConstantUnit T A).app U (a : A))) at hh
        have hconst := constantsIso_unit T A V (a : A)
        change ((constantsIso T).hom.app (CommRingCat.of A)).hom.app V
          ((adicLisseConstantUnit T A).app U (a : A)) =
            (ConstantCompletion.constantSection (J := smallTopology T) (a : A)).val V at hconst
        have hh' := congrArg
          ((ConstantCompletion.coefficientMap (smallTopology T) A I).hom.app V) hconst
        have hh := hh.trans hh'
        change f (β.inv.hom.app V
          ((ConstantCompletion.coefficientMap (smallTopology T) A I).hom.app V
            ((ConstantCompletion.constantSection (J := smallTopology T) (a : A)).val V))) = 0
        rw [← hh]
        exact (congrArg f (hβ _)).trans (hf a)
      | zero => simp only [map_zero]
      | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
      | smul a x _ hx =>
        change f (β.inv.hom.app V (a * x)) = 0
        rw [map_mul]
        change f ((β.inv.hom.app V a) • (β.inv.hom.app V x)) = 0
        rw [f.map_smul, hx, smul_zero]
    exact (congrArg f (hβ b)).symm.trans (hz' _ hz)

private theorem flat_presented_completion (T : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (e : adicLisseCompletedRing T I ≅ S) (c : adicLisseConstantRing T A ⟶ S)
    (hc : ∀ n : ℕ, c ≫ e.inv ≫ limit.π (adicLisseRingSystem T I) (op n) =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      ((SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj
        (SheafOfModules.unit ((adicLisseForget T).obj S))) := by
  classical
  let J := smallTopology T
  let R := ConstantCompletion.constant J A
  let B := ConstantCompletion.completed J A I
  let a := ConstantCompletion.coefficientMap J A I
  let M := (ConstantCompletion.res a).obj
    (SheafOfModules.unit (siteModuleRings B))
  have hm : SheafOfModules.IsFlatOnSite.{u + 1, u + 1, u + 1, u + 1} M := by
    let := SheafOfModules.monoidalCategory R
    exact ObjectProperty.prop_of_iso (exactFunctor _ _)
      (SheafOfModules.siteSheafTensorRightIso R M).symm
        (ConstantCompletion.flat_and_quotients J A I).1
  let α := (constantsIso T).app (CommRingCat.of A)
  let β := algebraIso T I e
  have hcomp := algebraIso_scalar T I e c hc
  let N := (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj
    (SheafOfModules.unit ((adicLisseForget T).obj S))
  apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion.{u + 1, u, u + 1, u + 1}
    (adicLisseConstantRing T A) N
  intro U n x y hxy
  let U' : smallSite T := AsSmall.up.obj U
  let x' : Fin n → R.obj.obj (op U') := fun i ↦ α.hom.hom.app (op U') (x i)
  let y' : Fin n → B.obj.obj (op U') := fun i ↦ β.hom.hom.app (op U') (y i)
  have hh : (∑ i, x' i • (show M.val.obj (op U') from y' i)) = 0 := by
    have h := congrArg (β.hom.hom.app (op U')) hxy
    rw [map_sum, map_zero] at h
    change (∑ i, a.hom.app (op U') (x' i) * y' i) = 0
    change (∑ i, β.hom.hom.app (op U')
      (c.hom.app (op U) (x i) * (show S.obj.obj (op U) from y i))) = 0 at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro i hi
    have heq := congrArg (fun k ↦ k.hom.app (op U') (x i)) hcomp
    change β.hom.hom.app (op U') (c.hom.app (op U) (x i)) =
      a.hom.app (op U') (α.hom.hom.app (op U') (x i)) at heq
    change a.hom.app (op U') (x' i) * y' i =
      β.hom.hom.app (op U') (c.hom.app (op U) (x i) * (show S.obj.obj (op U) from y i))
    rw [map_mul, heq]
  obtain ⟨K, hK, hrel⟩ :=
    SheafOfModules.local_equationalCriterion_of_isFlatOnSite.{u + 1, u + 1, u + 1, u + 1}
      R M hm U' n x' y' hh
  have hu : (AsSmall.up : T.ProEt ⥤ smallSite T).IsCocontinuous
      (ProEt.topology T) J := by
    apply ((AsSmall.equiv (C := T.ProEt)).toAdjunction.isCocontinuous_iff_coverPreserving
      (ProEt.topology T) J).2
    exact Functor.IsDenseSubsite.coverPreserving J (ProEt.topology T) AsSmall.down
  refine ⟨K.functorPullback AsSmall.up, AsSmall.up.cover_lift _ _ hK, ?_⟩
  intro V f hf
  obtain ⟨l, b, t₀, hy, hx⟩ := hrel (AsSmall.up.obj V) (AsSmall.up.map f) hf
  let t : Fin l → B.obj.obj (op (AsSmall.up.obj V)) := t₀
  change ∀ i, B.obj.map (AsSmall.up.map f).op (y' i) =
    ∑ j, a.hom.app (op (AsSmall.up.obj V)) (b i j) * t j at hy
  refine ⟨l, (fun i j ↦ α.inv.hom.app (op (AsSmall.up.obj V)) (b i j)),
    (fun j ↦ β.inv.hom.app (op (AsSmall.up.obj V)) (t j)), ?_, ?_⟩
  · intro i
    have heq := congrArg (β.inv.hom.app (op (AsSmall.up.obj V))) (hy i)
    rw [map_sum] at heq
    have hnat := ConcreteCategory.congr_hom (β.inv.hom.naturality
      (AsSmall.up.map f).op) (y' i)
    have hinv (z : S.obj.obj (op U)) :
        β.inv.hom.app (op (AsSmall.up.obj U))
          (β.hom.hom.app (op (AsSmall.up.obj U)) z) = z :=
      ConcreteCategory.congr_hom
        (congrArg (fun k ↦ k.hom.app (op (AsSmall.up.obj U))) β.hom_inv_id) z
    change S.obj.map f.op (y i) = _
    have hl : β.inv.hom.app (op (AsSmall.up.obj V))
        (B.obj.map (AsSmall.up.map f).op (y' i)) = S.obj.map f.op (y i) := by
      change β.inv.hom.app (op (AsSmall.up.obj V))
        (B.obj.map (AsSmall.up.map f).op (y' i)) = S.obj.map f.op
          (β.inv.hom.app (op (AsSmall.up.obj U)) (y' i)) at hnat
      exact hnat.trans (congrArg (S.obj.map f.op) (hinv (y i)))
    change β.inv.hom.app (op (AsSmall.up.obj V))
        (B.obj.map (AsSmall.up.map f).op (y' i)) = _ at heq
    rw [hl] at heq
    rw [heq]
    apply Finset.sum_congr rfl
    intro j hj
    have hs := congrArg (fun k ↦ k.hom.app (op (AsSmall.up.obj V))
      (α.inv.hom.app (op (AsSmall.up.obj V)) (b i j))) hcomp
    have ha : α.hom.hom.app (op (AsSmall.up.obj V))
        (α.inv.hom.app (op (AsSmall.up.obj V)) (b i j)) = b i j :=
      ConcreteCategory.congr_hom
        (congrArg (fun k ↦ k.hom.app (op (AsSmall.up.obj V))) α.inv_hom_id) _
    change β.hom.hom.app (op (AsSmall.up.obj V))
        (c.hom.app (op V) (α.inv.hom.app (op (AsSmall.up.obj V)) (b i j))) =
      a.hom.app (op (AsSmall.up.obj V))
        (α.hom.hom.app (op (AsSmall.up.obj V))
          (α.inv.hom.app (op (AsSmall.up.obj V)) (b i j))) at hs
    rw [ha] at hs
    change β.inv.hom.app (op (AsSmall.up.obj V))
        (a.hom.app (op (AsSmall.up.obj V)) (b i j) * t j) =
      c.hom.app (op V) (α.inv.hom.app (op (AsSmall.up.obj V)) (b i j)) *
        (show S.obj.obj (op V) from β.inv.hom.app (op (AsSmall.up.obj V)) (t j))
    rw [map_mul, ← hs]
    have hi := ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.hom.app (op (AsSmall.up.obj V))) β.hom_inv_id)
        (c.hom.app (op V) (α.inv.hom.app (op (AsSmall.up.obj V)) (b i j)))
    change β.inv.hom.app (op (AsSmall.up.obj V))
      (β.hom.hom.app (op (AsSmall.up.obj V))
        (c.hom.app (op V) (α.inv.hom.app (op (AsSmall.up.obj V)) (b i j)))) =
      c.hom.app (op V) (α.inv.hom.app (op (AsSmall.up.obj V)) (b i j)) at hi
    exact congrArg (fun z : S.obj.obj (op V) ↦ z *
      (show S.obj.obj (op V) from β.inv.hom.app (op (AsSmall.up.obj V)) (t j))) hi
  · intro j
    have heq := congrArg (α.inv.hom.app (op (AsSmall.up.obj V))) (hx j)
    rw [map_sum, map_zero] at heq
    change (∑ i, (adicLisseConstantRing T A).obj.map f.op (x i) *
      (show (adicLisseConstantRing T A).obj.obj (op V) from
        α.inv.hom.app (op (AsSmall.up.obj V)) (b i j))) = 0
    rw [← heq]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_mul]
    congr 1
    have hn := ConcreteCategory.congr_hom (α.inv.hom.naturality
      (AsSmall.up.map f).op) (x' i)
    have hinv := ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.hom.app (op (AsSmall.up.obj U))) α.hom_inv_id) (x i)
    change α.inv.hom.app (op (AsSmall.up.obj V))
        (R.obj.map (AsSmall.up.map f).op (x' i)) =
      (adicLisseConstantRing T A).obj.map f.op
        (α.inv.hom.app (op (AsSmall.up.obj U)) (x' i)) at hn
    change α.inv.hom.app (op (AsSmall.up.obj U))
      (α.hom.hom.app (op (AsSmall.up.obj U)) (x i)) = x i at hinv
    exact (hn.trans (congrArg ((adicLisseConstantRing T A).obj.map f.op) hinv)).symm

section

private local instance completedConstantAlgebraRestrictedModule (T : Scheme.{u})
    {A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj A))
    {X Y : T.ProEtᵒᵖ} (i : X ⟶ Y) :
    Module (A.obj.obj Y)
      ((ModuleCat.restrictScalars (((adicLisseForget T).obj A).obj.map i).hom).obj
        (M.val.obj Y)) :=
  inferInstanceAs (Module (A.obj.obj Y) (M.val.obj Y))

private theorem tensorRestriction_tmul
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S) (M : SheafOfModules.{u + 1}
      ((adicLisseForget T).obj A))
    {X Y : T.ProEtᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M).map i
      (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1} c M i) s m

end

private noncomputable def tensorToRestriction
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj A)) (H : SheafOfModules.{u + 1}
      ((adicLisseForget T).obj S))
    (f : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M ⟶ H.val) : M ⟶
      (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{u + 1, u + 1,
      u + 1}
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul T, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj A)) (H : SheafOfModules.{u + 1}
      ((adicLisseForget T).obj S))
    (g : M ⟶ (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj H) :
      SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
      (c.hom.app Y).hom (g.val.app Y)
        ((SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u
        + 1}
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul T, map_one]
    have atOne (W : T.ProEtᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
          W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj A)) (H : SheafOfModules.{u + 1}
      ((adicLisseForget T).obj S)) :
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M ⟶ H.val) ≃
      (M ⟶ (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj H) where
  toFun := tensorToRestriction T c M H
  invFun := restrictionToTensor T c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
      W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
      W).hom).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj A)) (H : SheafOfModules.{u + 1}
      ((adicLisseForget T).obj S)) :
    (SheafOfModules.changeOfRings.{u, u + 1, u + 1} c M ⟶ H) ≃ (M ⟶
      (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 ((adicLisseForget T).obj
    S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv T c M H)

private theorem tensorHomEquiv_tmul (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj R))
    (H : SheafOfModules.{u + 1} ((adicLisseForget T).obj S))
    (f : SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M ⟶ H)
    (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    f.val.app U ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)) =
      s • (@id (H.val.obj U) ((tensorHomEquiv T φ M H f).val.app U m)) := by
  let k := PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (𝟙 ((adicLisseForget T).obj S).obj) f
  change k.app U (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m) =
    s • k.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
  let k' : (ModuleCat.extendScalars (φ.hom.app U).hom).obj (M.val.obj U) ⟶
      H.val.obj U := k.app U
  have hh := k'.hom.map_smul s
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarTensorSectionIso (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : R ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj R)) :
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M).presheaf ≅
      (SheafOfModules.siteTensorPresheaf M.val
        ((SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj
          (SheafOfModules.unit ((adicLisseForget T).obj S))).val).presheaf := by
  letI (U : T.ProEtᵒᵖ) : Module (R.obj.obj U) (S.obj.obj U) :=
    Module.compHom _ (c.hom.app U).hom
  exact NatIso.ofComponents (fun U ↦ by
    letI : Module (R.obj.obj U) (S.obj.obj U) :=
      Module.compHom _ (c.hom.app U).hom
    exact AddEquiv.toAddCommGrpIso
      (X := AddCommGrpCat.of (TensorProduct (R.obj.obj U) (S.obj.obj U) (M.val.obj U)))
      (Y := AddCommGrpCat.of (TensorProduct (R.obj.obj U) (M.val.obj U) (S.obj.obj U)))
      (TensorProduct.comm (R.obj.obj U) (S.obj.obj U) (M.val.obj U)).toAddEquiv) (by
    intro U V f
    apply AddCommGrpCat.hom_ext
    ext z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m =>
      let : Module (R.obj.obj V)
          ((ModuleCat.restrictScalars (((adicLisseForget T).obj R).obj.map f).hom).obj
            (M.val.obj V)) :=
        inferInstanceAs (Module (R.obj.obj V) (M.val.obj V))
      change (TensorProduct.comm (R.obj.obj V) (S.obj.obj V) (M.val.obj V))
          ((SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M).map f
            (b ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] m)) =
        M.val.map f m ⊗ₜ[R.obj.obj V] S.obj.map f b
      rw [tensorRestriction_tmul T]
      rfl)

attribute [local irreducible] scalarTensorSectionIso

private noncomputable def scalarPresheafFunctor (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : R ⟶ S) :
    SheafOfModules.{u + 1} ((adicLisseForget T).obj R) ⥤
      _root_.PresheafOfModules.{u + 1} ((adicLisseForget T).obj S).obj where
  obj := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c
  map f :=
    { app := fun U ↦ (ModuleCat.extendScalars (c.hom.app U).hom).map (f.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality c _ f }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (c.hom.app U).hom).map_id (M.val.obj U)
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (c.hom.app U).hom).map_comp (f.val.app U) (g.val.app U)

private noncomputable def functorIsoOfObjMap
    {C D : Type*} [Category C] [Category D] (F G : C ⥤ D)
    (h : ∀ X, F.obj X = G.obj X)
    (hm : ∀ {X Y} (f : X ⟶ Y),
      F.map f = eqToHom (h X) ≫ G.map f ≫ eqToHom (h Y).symm) : F ≅ G :=
  NatIso.ofComponents (fun X ↦ eqToIso (h X)) (by
    intro X Y f
    dsimp only [eqToIso.hom]
    rw [hm]
    simp)

private noncomputable def scalarTensorRawIso (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : R ⟶ S) :
    scalarPresheafFunctor T c ⋙ PresheafOfModules.toPresheaf _ ≅
      SheafOfModules.forget _ ⋙ SheafOfModules.siteTensorRight
        ((SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj
          (SheafOfModules.unit ((adicLisseForget T).obj S))).val ⋙
        PresheafOfModules.toPresheaf _ :=
  NatIso.ofComponents (fun M ↦ scalarTensorSectionIso T c M) (by
    intro M M' f
    unfold scalarPresheafFunctor
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    ext z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m =>
      unfold scalarTensorSectionIso
      rfl)

attribute [local irreducible] scalarTensorRawIso

private noncomputable def scalarTensorIso (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : R ⟶ S) :
    completedAdicChange T c ⋙ SheafOfModules.toSheaf.{u + 1} ((adicLisseForget T).obj S) ≅
      SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (J := ProEt.topology T) (A := R)
        ((SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj
          (SheafOfModules.unit ((adicLisseForget T).obj S))) ⋙
        SheafOfModules.toSheaf.{u + 1} ((adicLisseForget T).obj R) := by
  let a := PresheafOfModules.sheafification.{u + 1}
    (𝟙 ((adicLisseForget T).obj S).obj)
  let G := scalarPresheafFunctor T c ⋙ a
  let e : completedAdicChange T c ≅ G := functorIsoOfObjMap _ _
    ((completedAdicChangeData T c).choose_spec.choose)
    (fun f ↦ (completedAdicChangeData T c).choose_spec.choose_spec.choose f)
  refine Functor.isoWhiskerRight e (SheafOfModules.toSheaf.{u + 1} _) ≪≫ ?_
  exact Functor.isoWhiskerRight (scalarTensorRawIso T c)
    (presheafToSheaf (ProEt.topology T) AddCommGrpCat.{u + 1})

private theorem forget_preserves_colimits (T : Scheme.{u})
    (A : Sheaf (ProEt.topology T) RingCat.{u + 1}) :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} A) := by
  constructor
  intro K _ _
  constructor
  intro F
  let L := PresheafOfModules.sheafification.{u + 1} (𝟙 A.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 A.obj)
  let G := F ⋙ (SheafOfModules.forget A ⋙ PresheafOfModules.restrictScalars (𝟙 A.obj))
  let e : G ⋙ L ≅ F := Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ F.rightUnitor
  have : PreservesColimitsOfShape K (presheafToSheaf (ProEt.topology T) AddCommGrpCat.{u + 1}) :=
    (Adjunction.leftAdjoint_preservesColimits
      (sheafificationAdjunction (ProEt.topology T) AddCommGrpCat.{u + 1}))
      |>.preservesColimitsOfShape
  have : PreservesColimit G (L ⋙ SheafOfModules.toSheaf.{u + 1} A) :=
    preservesColimit_of_natIso G
      (PresheafOfModules.sheafificationCompToSheaf.{u + 1} (𝟙 A.obj)).symm
  let hc := colimit.isColimit G
  have : PreservesColimit (G ⋙ L) (SheafOfModules.toSheaf.{u + 1} A) :=
    preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves L hc)
      (isColimitOfPreserves (L ⋙ SheafOfModules.toSheaf.{u + 1} A) hc)
  exact preservesColimit_of_iso_diagram (SheafOfModules.toSheaf.{u + 1} A) e

private theorem scalar_exact_of_flat (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : R ⟶ S)
    (h : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      ((SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj
        (SheafOfModules.unit ((adicLisseForget T).obj S)))) :
    exactFunctor _ _ (completedAdicChange T c) := by
  let F := SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
    ((SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj
      (SheafOfModules.unit ((adicLisseForget T).obj S)))
  have : PreservesFiniteLimits F := h.1
  have : PreservesFiniteColimits F := h.2
  have := forget_preserves_colimits T ((adicLisseForget T).obj R)
  have := forget_preserves_colimits T ((adicLisseForget T).obj S)
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u + 1} ((adicLisseForget T).obj S)) :=
    inferInstance
  have hh : exactFunctor _ _
      (completedAdicChange T c ⋙ SheafOfModules.toSheaf.{u + 1} ((adicLisseForget T).obj S)) :=
    ObjectProperty.prop_of_iso (exactFunctor _ _) (scalarTensorIso T c).symm
      ⟨comp_preservesFiniteLimits F (SheafOfModules.toSheaf.{u + 1} _),
        comp_preservesFiniteColimits F (SheafOfModules.toSheaf.{u + 1} _)⟩
  have : PreservesFiniteLimits
      (completedAdicChange T c ⋙ SheafOfModules.toSheaf.{u + 1} ((adicLisseForget T).obj S)) := hh.1
  have : PreservesFiniteColimits
      (completedAdicChange T c ⋙ SheafOfModules.toSheaf.{u + 1} ((adicLisseForget T).obj S)) := hh.2
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves (completedAdicChange T c)
    (SheafOfModules.toSheaf.{u + 1} _),
    preservesFiniteColimits_of_reflects_of_preserves (completedAdicChange T c)
      (SheafOfModules.toSheaf.{u + 1} _)⟩

private noncomputable def descendLinearSurj {R M N : Type (u + 1)} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : R →ₗ[R] M) (hf : Function.Surjective f) (g : R →ₗ[R] N)
    (h : LinearMap.ker f ≤ LinearMap.ker g) : M →ₗ[R] N :=
  ((LinearMap.ker f).liftQ g h).comp (f.quotKerEquivOfSurjective hf).symm.toLinearMap

private theorem descendLinearSurj_apply {R M N : Type (u + 1)} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : R →ₗ[R] M) (hf : Function.Surjective f) (g : R →ₗ[R] N)
    (h : LinearMap.ker f ≤ LinearMap.ker g) (x : R) :
    descendLinearSurj f hf g h (f x) = g x := by
  unfold descendLinearSurj
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

private theorem quotient_isIso (T : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (e : adicLisseCompletedRing T I ≅ S) (c : adicLisseConstantRing T A ⟶ S)
    (hc : ∀ n : ℕ, c ≫ e.inv ≫ limit.π (adicLisseRingSystem T I) (op n) =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
    (n : ℕ) (H : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (d : adicLisseConstantRing T (A ⧸ I ^ (n + 1)) ≅ H) (p : S ⟶ H)
    (hp : p = e.inv ≫ limit.π (adicLisseRingSystem T I) (op n) ≫ d.hom)
    (r : (completedAdicChange T c).obj
      ((adicLisseConstantModules T A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1)))) ⟶
        (SheafOfModules.restrictScalars ((adicLisseForget T).map p)).obj
          (SheafOfModules.unit ((adicLisseForget T).obj H)))
    (hr : ∀ (U : T.ProEtᵒᵖ) (b : S.obj.obj U) (x : A ⧸ I ^ (n + 1)),
      r.val.app U (tensorSection T c _ U b
        ((toSheafify (ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (AddCommGrpCat.of (ModuleCat.of A (A ⧸ I ^ (n + 1)))))).app U x)) =
          p.hom.app U b * d.hom.hom.app U
            ((adicLisseConstantUnit T (A ⧸ I ^ (n + 1))).app U x)) : IsIso r := by
  classical
  let Q := A ⧸ I ^ (n + 1)
  let P : _root_.PresheafOfModules.{u + 1}
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) :=
    (siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
      PresheafOfModules.pushforward₀
        ((Functor.const T.ProEt).obj (Discrete.mk (ULift.up ())))
        ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))).obj
          (ModuleCat.of A Q)
  let M := (adicLisseConstantModules T A).obj (ModuleCat.of A Q)
  let Z := (SheafOfModules.restrictScalars ((adicLisseForget T).map p)).obj
    (SheafOfModules.unit ((adicLisseForget T).obj H))
  let q := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M
  let X := SheafOfModules.changeOfRings.{u, u + 1, u + 1} c M
  let η₀ := (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (adicLisseConstantUnit T A)).unit.app P
  let η (U : T.ProEtᵒᵖ) (x : Q) : M.val.obj U := η₀.app U x
  let κ := (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((adicLisseForget T).obj S).obj)).unit.app q
  let h := (completedAdicChangeData T c).choose_spec.choose M
  let r₀ : X ⟶ Z := eqToHom h.symm ≫ r
  have hr₀ (U : T.ProEtᵒᵖ) (b : S.obj.obj U) (x : Q) :
      r₀.val.app U ((κ.app U)
        (b ⊗ₜ[(adicLisseConstantRing T A).obj.obj U, (c.hom.app U).hom] (η U x))) =
          p.hom.app U b * d.hom.hom.app U ((adicLisseConstantUnit T Q).app U x) :=
    hr U b x
  let z (U : T.ProEtᵒᵖ) : X.val.obj U := (κ.app U)
    ((1 : S.obj.obj U) ⊗ₜ[(adicLisseConstantRing T A).obj.obj U,
      (c.hom.app U).hom] (η U 1))
  let zs : X.sections := PresheafOfModules.sectionsMk z (by
    intro U V f
    have hη := ConcreteCategory.congr_hom (η₀.naturality f) (1 : Q)
    change η V (1 : Q) = M.val.map f (η U (1 : Q)) at hη
    have ht := PresheafOfModules.naturality_apply κ f
      ((1 : S.obj.obj U) ⊗ₜ[(adicLisseConstantRing T A).obj.obj U,
        (c.hom.app U).hom] (η U 1))
    change (κ.app V) (q.map f ((1 : S.obj.obj U) ⊗ₜ[
      (adicLisseConstantRing T A).obj.obj U, (c.hom.app U).hom] (η U 1))) =
        X.val.map f (z U) at ht
    rw [tensorRestriction_tmul T, map_one, ← hη] at ht
    exact ht.symm)
  let t : SheafOfModules.unit ((adicLisseForget T).obj S) ⟶ X := X.unitHomEquiv.symm zs
  have ht (U : T.ProEtᵒᵖ) (b : S.obj.obj U) : t.val.app U b = b • z U := rfl
  have ht_scalar (U : T.ProEtᵒᵖ) (a : A) :
      t.val.app U (c.hom.app U ((adicLisseConstantUnit T A).app U a)) =
        (κ.app U) ((1 : S.obj.obj U) ⊗ₜ[(adicLisseConstantRing T A).obj.obj U,
          (c.hom.app U).hom] (η U (Ideal.Quotient.mk (I ^ (n + 1)) a))) := by
    rw [ht]
    change _ • ((κ.app U).hom _) = (κ.app U).hom _
    rw [← (κ.app U).hom.map_smul]
    congr 1
    have hη := (η₀.app U).hom.map_smul a (1 : Q)
    change η U ((Ideal.Quotient.mk (I ^ (n + 1)) a) * 1) =
      ((adicLisseConstantUnit T A).app U a) • (η U 1) at hη
    rw [mul_one] at hη
    rw [hη]
    let : Module ((adicLisseConstantRing T A).obj.obj U) (S.obj.obj U) :=
      Module.compHom _ (c.hom.app U).hom
    change (c.hom.app U ((adicLisseConstantUnit T A).app U a) * 1) ⊗ₜ[
        (adicLisseConstantRing T A).obj.obj U, (c.hom.app U).hom] (η U 1) =
      (1 : S.obj.obj U) ⊗ₜ[(adicLisseConstantRing T A).obj.obj U,
        (c.hom.app U).hom] (((adicLisseConstantUnit T A).app U a) • η U 1)
    exact TensorProduct.smul_tmul
      (R := (adicLisseConstantRing T A).obj.obj U)
      (show (adicLisseConstantRing T A).obj.obj U from
        (adicLisseConstantUnit T A).app U a) (1 : S.obj.obj U) (η U 1)
  let l (U : T.ProEtᵒᵖ) : S.obj.obj U →ₗ[S.obj.obj U] Z.val.obj U :=
    { toFun := fun b ↦ p.hom.app U b
      map_add' := map_add (p.hom.app U).hom
      map_smul' := fun b b' ↦ map_mul (p.hom.app U).hom b b' }
  have hsurj (U : T.ProEtᵒᵖ) : Function.Surjective (l U) :=
    (projection_surjective_and_kernel T I e c hc n d p hp U).1
  have hker (U : T.ProEtᵒᵖ) : LinearMap.ker (l U) ≤ LinearMap.ker (t.val.app U).hom := by
    intro b hb
    apply (projection_surjective_and_kernel T I e c hc n d p hp U).2
      (X.val.obj U) (t.val.app U).hom ?_ b hb
    intro a
    change t.val.app U
      (c.hom.app U ((adicLisseConstantUnit T A).app U (a : A))) = 0
    rw [ht_scalar]
    have ha : Ideal.Quotient.mk (I ^ (n + 1)) (a : A) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr a.property
    rw [ha]
    change (κ.app U).hom ((1 : S.obj.obj U) ⊗ₜ[
      (adicLisseConstantRing T A).obj.obj U, (c.hom.app U).hom] ((η₀.app U).hom 0)) = 0
    rw [map_zero, TensorProduct.tmul_zero, map_zero]
  let sU (U : T.ProEtᵒᵖ) : Z.val.obj U →ₗ[S.obj.obj U] X.val.obj U :=
    descendLinearSurj (l U) (hsurj U) (t.val.app U).hom (hker U)
  have hsU (U : T.ProEtᵒᵖ) (b : S.obj.obj U) : sU U (p.hom.app U b) = t.val.app U b :=
    descendLinearSurj_apply (l U) (hsurj U) (t.val.app U).hom (hker U) b
  let s : Z ⟶ X :=
    { val :=
      { app := fun U ↦ ModuleCat.ofHom
          (X := Z.val.obj U) (Y := X.val.obj U) (sU U)
        naturality := by
          intro U V f
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro y
          obtain ⟨b, rfl⟩ := hsurj U y
          change sU V (H.obj.map f (p.hom.app U b)) = X.val.map f (sU U (p.hom.app U b))
          have hn := NatTrans.naturality_apply p.hom f b
          rw [← hn, hsU, hsU]
          exact PresheafOfModules.naturality_apply t.val f b } }
  have hscalar (U : T.ProEtᵒᵖ) (a : A) :
      d.hom.hom.app U ((adicLisseConstantUnit T Q).app U
        (Ideal.Quotient.mk (I ^ (n + 1)) a)) =
          p.hom.app U (c.hom.app U ((adicLisseConstantUnit T A).app U a)) := by
    have hh : c ≫ p =
        (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ d.hom := by
      calc
        c ≫ p = (c ≫ e.inv ≫ limit.π (adicLisseRingSystem T I) (op n)) ≫ d.hom := by
          rw [hp]
          simp only [Category.assoc]
        _ = _ := congrArg (fun k ↦ k ≫ d.hom) (hc n)
    have hn := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app U)
      (toSheafify_naturality (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))) a
    have hhh := congrArg (fun k ↦ k.hom.app U ((adicLisseConstantUnit T A).app U a)) hh
    change p.hom.app U (c.hom.app U ((adicLisseConstantUnit T A).app U a)) =
      d.hom.hom.app U (((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))).hom.app U
          ((adicLisseConstantUnit T A).app U a)) at hhh
    change (adicLisseConstantUnit T Q).app U (Ideal.Quotient.mk (I ^ (n + 1)) a) =
      (((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))).hom.app U
          ((adicLisseConstantUnit T A).app U a)) at hn
    exact (congrArg (d.hom.hom.app U) hn).trans hhh.symm
  let j : X ≅ Z :=
    { hom := r₀
      inv := s
      hom_inv_id := by
        apply (tensorHomEquiv T c M X).injective
        apply (PresheafOfModules.sheafificationHomEquiv.{u + 1}
          (adicLisseConstantUnit T A) (P := P) (F :=
            (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj X)).injective
        apply PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        have hl := tensorHomEquiv_tmul T c M X (r₀ ≫ s) U 1
          (η U (Ideal.Quotient.mk (I ^ (n + 1)) a))
        have hi := tensorHomEquiv_tmul T c M X (𝟙 X) U 1
          (η U (Ideal.Quotient.mk (I ^ (n + 1)) a))
        simp only [one_smul, id_eq] at hl hi
        change (tensorHomEquiv T c M X (r₀ ≫ s)).val.app U
          (η U (Ideal.Quotient.mk (I ^ (n + 1)) a)) =
            (tensorHomEquiv T c M X (𝟙 X)).val.app U
              (η U (Ideal.Quotient.mk (I ^ (n + 1)) a))
        rw [← hl, ← hi]
        change sU U (r₀.val.app U ((κ.app U) _)) = _
        rw [hr₀, map_one, one_mul, hscalar, hsU, ht_scalar]
        rfl
      inv_hom_id := by
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        obtain ⟨b, rfl⟩ := hsurj U y
        change r₀.val.app U (sU U (p.hom.app U b)) = p.hom.app U b
        rw [hsU, ht]
        change (r₀.val.app U).hom (b • z U) = _
        rw [(r₀.val.app U).hom.map_smul]
        have hz : r₀.val.app U (z U) = (1 : H.obj.obj U) := by
          change r₀.val.app U ((κ.app U) ((1 : S.obj.obj U) ⊗ₜ[
            (adicLisseConstantRing T A).obj.obj U, (c.hom.app U).hom] (η U 1))) = _
          rw [hr₀, map_one, map_one, map_one, one_mul]
        rw [hz]
        change p.hom.app U b * 1 = p.hom.app U b
        exact mul_one _ }
  have : IsIso r₀ := j.isIso_hom
  have hh : r = eqToHom h ≫ r₀ := by simp [r₀]
  rw [hh]
  infer_instance

end CompletedConstantAlgebra

/-- Completion of a Noetherian constant algebra is flat, scalar extension is exact,
and the projection-multiplication map to each constant quotient is invertible.
The result retains arbitrary isomorphic presentations of the completed and quotient rings.
Source: Stacks Project, sites-modules.tex, Tag 093M, lemma-completion-flat, and its
quotient assertion applied to each power of the ideal.
(auxiliary; not a blueprint node)

Proof: Pass to the coefficient-sized equivalent `AsSmall` site with its induced topology.
The continuous-pushforward/sheafification comparison identifies constant sheaves, with
their sheafification units. Its naturality identifies the quotient diagrams; preservation
of limits identifies their completions and all projection maps. Apply the flatness and
sectionwise quotient-kernel theorem `ConstantCompletion.flat_and_quotients` there.
For flatness on the original site, transport each finite relation across the ring
isomorphisms, obtain local factorizations by the forward equational criterion, pull the
covering sieve back along the inverse site equivalence, and transport the witnesses back.
The converse local criterion gives flatness. Interchanging sectionwise tensor factors
and then sheafifying identifies underlying scalar extension with tensor by this flat
algebra. Forgetting to additive sheaves preserves and reflects finite limits and
colimits, so scalar extension is exact.
For the quotient assertion, transport surjectivity and the generated-kernel formula
back to the original site. In the scalar extension X of the constant quotient module,
the section z=1 tensor 1 defines t:S→X. Balancedness gives t(c(a))=1 tensor class(a),
which vanishes for a in I^(n+1). Induction on ideal-span membership proves ker(p)≤ker(t).
Descend t sectionwise through the surjective map p to construct s:H→X. Naturality follows
by lifting a section of H through p and using naturality of t. The formula for r gives
r(s(p(b)))=p(b). For the other identity use the scalar-tensor and constant-sheafification
adjunctions: quotient surjectivity reduces to a class represented by a in A, and
s(r(1 tensor class(a)))=s(p(c(a)))=t(c(a))=1 tensor class(a). Thus both inverse identities
hold. Specified ring isomorphisms preserve all formulas. Zero rings, I=0, I=A and empty
covering sieves require no extra hypotheses. -/
theorem completed_constant_algebra_flat_quotients
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (e : adicLisseCompletedRing T I ≅ S) (c : adicLisseConstantRing T A ⟶ S)
    (hc : ∀ n : ℕ, c ≫ e.inv ≫ limit.π (adicLisseRingSystem T I) (op n) =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) :
    SheafOfModules.IsFlatOnSite
      ((SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj
        (SheafOfModules.unit ((adicLisseForget T).obj S))) ∧
    exactFunctor _ _ (completedAdicChange T c) ∧
    ∀ (n : ℕ) (H : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
      (d : adicLisseConstantRing T (A ⧸ I ^ (n + 1)) ≅ H)
      (p : S ⟶ H)
      (_hp : p = e.inv ≫ limit.π (adicLisseRingSystem T I) (op n) ≫ d.hom)
      (r : (completedAdicChange T c).obj
        ((adicLisseConstantModules T A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1)))) ⟶
          (SheafOfModules.restrictScalars ((adicLisseForget T).map p)).obj
            (SheafOfModules.unit ((adicLisseForget T).obj H))),
      (∀ (U : T.ProEtᵒᵖ) (b : S.obj.obj U) (x : A ⧸ I ^ (n + 1)),
        r.val.app U (tensorSection T c _ U b
          ((toSheafify (ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj
              (AddCommGrpCat.of (ModuleCat.of A (A ⧸ I ^ (n + 1)))))).app U x)) =
            p.hom.app U b * d.hom.hom.app U
              ((adicLisseConstantUnit T (A ⧸ I ^ (n + 1))).app U x)) → IsIso r := by
  have h := CompletedConstantAlgebra.flat_presented_completion T I e c hc
  refine ⟨h, CompletedConstantAlgebra.scalar_exact_of_flat T c h, ?_⟩
  intro n H d p hp r hr
  exact CompletedConstantAlgebra.quotient_isIso T I S e c hc n H d p hp r hr

end AlgebraicGeometry.Scheme
