/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedReductionUnit
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulRoosComparison
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Transport of the two strict completion presentations to the small constant site

Source: Stacks Tags 03CR, 05RR, 06YY and 0941.
(blueprint: lem-weil-pbc-completed-constant-coefficient-equivalence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

namespace CechConstantAlgebra
open AdicCoefficients

private abbrev smallSite (T : Scheme.{t}) := AsSmall.{0} T.ProEt
private abbrev smallTopology (T : Scheme.{t}) :=
  (AsSmall.down : smallSite T ⥤ T.ProEt).inducedTopology (ProEt.topology T)
private instance down_isEquivalence (T : Scheme.{t}) :
    (AsSmall.down : smallSite T ⥤ T.ProEt).IsEquivalence :=
  inferInstanceAs ((AsSmall.equiv (C := T.ProEt)).inverse.IsEquivalence)
private instance down_isDenseSubsite (T : Scheme.{t}) :
    (AsSmall.down : smallSite T ⥤ T.ProEt).IsDenseSubsite
      (smallTopology T) (ProEt.topology T) := by
  change (AsSmall.down : smallSite T ⥤ T.ProEt).IsDenseSubsite
    ((AsSmall.down : smallSite T ⥤ T.ProEt).inducedTopology (ProEt.topology T))
    (ProEt.topology T)
  infer_instance
private noncomputable def constantsIso (T : Scheme.{t}) :
    constantSheaf (ProEt.topology T) CommRingCat.{t + 1} ⋙
      (AsSmall.down : smallSite T ⥤ T.ProEt).sheafPushforwardContinuous
        CommRingCat.{t + 1} (smallTopology T) (ProEt.topology T) ≅
      constantSheaf (smallTopology T) CommRingCat.{t + 1} :=
  NatIso.ofComponents (fun A ↦
    ((AsSmall.down : smallSite T ⥤ T.ProEt).pushforwardContinuousSheafificationCompatibility
        CommRingCat.{t + 1} (smallTopology T) (ProEt.topology T)).symm.app
          ((Functor.const T.ProEtᵒᵖ).obj A)) (by
    intro A B f
    exact ((AsSmall.down : smallSite T ⥤ T.ProEt).pushforwardContinuousSheafificationCompatibility
        CommRingCat.{t + 1} (smallTopology T) (ProEt.topology T)).inv.naturality
          ((Functor.const T.ProEtᵒᵖ).map f))

attribute [local irreducible] constantsIso

private abbrev pushRing (T : Scheme.{t}) :=
  (AsSmall.down : smallSite T ⥤ T.ProEt).sheafPushforwardContinuous
    CommRingCat.{t + 1} (smallTopology T) (ProEt.topology T)
private noncomputable def systemIso (T : Scheme.{t}) {A : Type (t + 1)}
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

private noncomputable def completionIso (T : Scheme.{t}) {A : Type (t + 1)}
    [CommRing A] (I : Ideal A) :
    (pushRing T).obj (adicLisseCompletedRing T I) ≅
      ConstantCompletion.completed (smallTopology T) A I :=
  preservesLimitIso (pushRing T) (adicLisseRingSystem T I) ≪≫
    lim.mapIso (systemIso T I)

attribute [local irreducible] completionIso

private theorem completionIso_projection (T : Scheme.{t}) {A : Type (t + 1)}
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

private theorem coefficientMap_eq (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (I : Ideal A) (c : adicLisseConstantRing T A ⟶ adicLisseCompletedRing T I)
    (hc : ∀ n : ℕ, c ≫ limit.π (adicLisseRingSystem T I) (op n) =
      (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
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

private noncomputable def algebraIso (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (I : Ideal A) {S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (e : adicLisseCompletedRing T I ≅ S) :
    (pushRing T).obj S ≅ ConstantCompletion.completed (smallTopology T) A I :=
  (pushRing T).mapIso e.symm ≪≫ completionIso T I

attribute [local irreducible] algebraIso

private theorem algebraIso_scalar (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (I : Ideal A) {S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (e : adicLisseCompletedRing T I ≅ S) (c : adicLisseConstantRing T A ⟶ S)
    (hc : ∀ n : ℕ, c ≫ e.inv ≫ limit.π (adicLisseRingSystem T I) (op n) =
      (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) :
    (pushRing T).map c ≫ (algebraIso T I e).hom =
      (constantsIso T).hom.app (CommRingCat.of A) ≫
        ConstantCompletion.coefficientMap (smallTopology T) A I := by
  unfold algebraIso
  dsimp only [ Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Functor.map_comp]
  exact coefficientMap_eq T I (c ≫ e.inv) (fun n ↦ by rw [Category.assoc]; exact hc n)

private theorem constantsIso_unit (T : Scheme.{t}) (A : Type (t + 1)) [CommRing A]
    (U : (smallSite T)ᵒᵖ) (a : A) :
    ((constantsIso T).hom.app (CommRingCat.of A)).hom.app U
        ((adicLisseConstantUnit T A).app (AsSmall.down.op.obj U) a) =
      (ConstantCompletion.constantSection (J := smallTopology T) a).val U := by
  have h := Functor.toSheafify_pullbackSheafificationCompatibility
    (AsSmall.down : smallSite T ⥤ T.ProEt) CommRingCat.{t + 1}
      (smallTopology T) (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))
  have h' := congrArg (fun k ↦ k.app U) h
  have h'' := ConcreteCategory.congr_hom h' a
  unfold constantsIso
  change ((AsSmall.down.pushforwardContinuousSheafificationCompatibility
    CommRingCat.{t + 1} (smallTopology T) (ProEt.topology T)).inv.app
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).hom.app U
        ((adicLisseConstantUnit T A).app (AsSmall.down.op.obj U) a) = _
  refine (congrArg (fun z ↦
    ((AsSmall.down.pushforwardContinuousSheafificationCompatibility
      CommRingCat.{t + 1} (smallTopology T) (ProEt.topology T)).inv.app
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).hom.app U z) h'').symm.trans ?_
  exact ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U)
    ((AsSmall.down.pushforwardContinuousSheafificationCompatibility
      CommRingCat.{t + 1} (smallTopology T) (ProEt.topology T)).app
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).hom_inv_id) _

private theorem projection_transport (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (I : Ideal A) {S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (e : adicLisseCompletedRing T I ≅ S) (n : ℕ)
    {H : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
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

private theorem projection_surjective (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (e : adicLisseCompletedRing T I ≅ S)
    (n : ℕ) {H : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (d : adicLisseConstantRing T (A ⧸ I ^ (n + 1)) ≅ H) (p : S ⟶ H)
    (hp : p = e.inv ≫ limit.π (adicLisseRingSystem T I) (op n) ≫ d.hom)
    (U : T.ProEtᵒᵖ) :
    Function.Surjective (p.hom.app U) := by
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
  have hβ' (b : B.obj.obj V) : β.hom.hom.app V (β.inv.hom.app V b) = b :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app V) β.inv_hom_id) b
  have hδ (b : H.obj.obj U) : δ.inv.hom.app V (δ.hom.hom.app V b) = b :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app V) δ.hom_inv_id) b
  obtain ⟨hsurj, _⟩ :=
    (ConstantCompletion.flat_and_quotients (smallTopology T) A I).2.1 n V.unop
  intro y
  obtain ⟨b, hb⟩ := hsurj (δ.hom.hom.app V y)
  refine ⟨β.inv.hom.app V b, ?_⟩
  have hh := heq (β.inv.hom.app V b)
  change (ConstantCompletion.projection (smallTopology T) A I n).hom.app V
    (β.hom.hom.app V (β.inv.hom.app V b)) =
      δ.hom.hom.app V (p.hom.app U (β.inv.hom.app V b)) at hh
  rw [hβ', hb] at hh
  exact (hδ _).symm.trans ((congrArg (δ.inv.hom.app V) hh).symm.trans (hδ _))

end CechConstantAlgebra

attribute [local irreducible] CechConstantAlgebra.algebraIso
  CechConstantAlgebra.constantsIso CechConstantAlgebra.completionIso
  CechConstantAlgebra.systemIso

private abbrev comparisonTopology (T : Scheme.{t}) :=
  CechConstantAlgebra.smallTopology T

private instance comparisonAbLocallyBijective (T : Scheme.{t}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T

private abbrev comparisonRing (T : Scheme.{t}) {A : Type (t + 1)}
    [CommRing A] (d : AdicCoefficientDatum A) :=
  ConstantCompletion.completed (comparisonTopology T) A d.ideal

private def smallModulesEquiv (T : Scheme.{t})
    (R₀ : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (B : Sheaf (comparisonTopology T) CommRingCat.{t + 1})
    (β₀ : (CechConstantAlgebra.pushRing T).obj R₀ ≅ B) :
    reductionModules T R₀ ≌ ConstantCompletion.Mod B := by
  let e := completedCechSiteEquiv T
  let J := ProEt.topology T
  let L := comparisonTopology T
  let : e.functor.IsContinuous J L :=
    inferInstanceAs ((completedCechSiteEquiv T).functor.IsContinuous
      (ProEt.topology T) ((completedCechSiteEquiv T).inverse.inducedTopology
        (ProEt.topology T)))
  let : e.inverse.IsContinuous L J :=
    inferInstanceAs ((completedCechSiteEquiv T).inverse.IsContinuous
      ((completedCechSiteEquiv T).inverse.inducedTopology (ProEt.topology T))
      (ProEt.topology T))
  let R := reductionModuleRing T R₀
  let S := siteModuleRings B
  let β := (sheafCompose L (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).mapIso
    β₀
  let φ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{t + 1} J L).obj S :=
    ⟨{ app := fun U ↦ β.hom.hom.app (e.functor.op.obj U)
       naturality := fun _ _ f ↦ β.hom.hom.naturality (e.functor.op.map f) }⟩
  let ψ : S ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{t + 1} L J).obj R :=
    β.inv
  have h₁ : Functor.whiskerRight (NatTrans.op e.counit) S.obj =
      ψ.hom ≫ e.inverse.op.whiskerLeft φ.hom := by
    apply NatTrans.ext
    funext U
    rcases U with ⟨⟨U⟩⟩
    change S.obj.map (e.counit.app (AsSmall.up.obj U)).op =
      β.inv.hom.app (op (AsSmall.up.obj U)) ≫ β.hom.hom.app (op (AsSmall.up.obj U))
    have h := congrArg (fun k ↦ k.hom.app (op (AsSmall.up.obj U))) β.inv_hom_id
    change S.obj.map (𝟙 _) = _
    rw [S.obj.map_id]
    exact h.symm
  have h₂ : φ.hom ≫ e.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.unit) R.obj = 𝟙 R.obj := by
    apply NatTrans.ext
    funext U
    change β.hom.hom.app (e.functor.op.obj U) ≫
      β.inv.hom.app (e.functor.op.obj U) ≫ R.obj.map (e.unit.app U.unop).op = 𝟙 _
    rw [show R.obj.map (e.unit.app U.unop).op = 𝟙 _ from R.obj.map_id _]
    erw [Category.comp_id]
    exact congrArg (fun k ↦ k.hom.app (e.functor.op.obj U)) β.hom_inv_id
  exact (SheafOfModules.pushforwardPushforwardEquivalence.{t + 1} e φ ψ h₁ h₂).symm

private def smallRestrictionComparison (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {B H : Sheaf (comparisonTopology T) CommRingCat.{t + 1}}
    (β : (CechConstantAlgebra.pushRing T).obj R ≅ B)
    (δ : (CechConstantAlgebra.pushRing T).obj S ≅ H)
    (p : R ⟶ S) (q : B ⟶ H)
    (hp : β.hom ≫ q = (CechConstantAlgebra.pushRing T).map p ≫ δ.hom) :
    (smallModulesEquiv T S H δ).inverse ⋙
        SheafOfModules.restrictScalars ((adicLisseForget T).map p) ≅
      ConstantCompletion.res q ⋙ (smallModulesEquiv T R B β).inverse := by
  have hc (U : T.ProEtᵒᵖ) (r : R.obj.obj U) :
      δ.hom.hom.app (AsSmall.up.op.obj U) (p.hom.app U r) =
        q.hom.app (AsSmall.up.op.obj U) (β.hom.hom.app (AsSmall.up.op.obj U) r) := by
    exact (ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.hom.app (AsSmall.up.op.obj U)) hp) r).symm
  let f (M : ConstantCompletion.Mod H) :
      ((smallModulesEquiv T S H δ).inverse ⋙
        SheafOfModules.restrictScalars ((adicLisseForget T).map p)).obj M ⟶
      (ConstantCompletion.res q ⋙ (smallModulesEquiv T R B β).inverse).obj M :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
        (X := (((smallModulesEquiv T S H δ).inverse ⋙
            SheafOfModules.restrictScalars ((adicLisseForget T).map p)).obj M).val.obj U)
        (Y := ((ConstantCompletion.res q ⋙ (smallModulesEquiv T R B β).inverse).obj M).val.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun r x ↦ by
            change δ.hom.hom.app (AsSmall.up.op.obj U) (p.hom.app U r) •
                (show M.val.obj (AsSmall.up.op.obj U) from x) =
              q.hom.app (AsSmall.up.op.obj U)
                (β.hom.hom.app (AsSmall.up.op.obj U) r) •
                  (show M.val.obj (AsSmall.up.op.obj U) from x)
            rw [hc] }
       naturality := fun _ ↦ by ext x; rfl }⟩
  let g (M : ConstantCompletion.Mod H) :
      (ConstantCompletion.res q ⋙ (smallModulesEquiv T R B β).inverse).obj M ⟶
      ((smallModulesEquiv T S H δ).inverse ⋙
        SheafOfModules.restrictScalars ((adicLisseForget T).map p)).obj M :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
        (X := ((ConstantCompletion.res q ⋙ (smallModulesEquiv T R B β).inverse).obj M).val.obj U)
        (Y := (((smallModulesEquiv T S H δ).inverse ⋙
            SheafOfModules.restrictScalars ((adicLisseForget T).map p)).obj M).val.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun r x ↦ by
            change q.hom.app (AsSmall.up.op.obj U)
                (β.hom.hom.app (AsSmall.up.op.obj U) r) •
                  (show M.val.obj (AsSmall.up.op.obj U) from x) =
              δ.hom.hom.app (AsSmall.up.op.obj U) (p.hom.app U r) •
                (show M.val.obj (AsSmall.up.op.obj U) from x)
            rw [hc] }
       naturality := fun _ ↦ by ext x; rfl }⟩
  exact NatIso.ofComponents (fun M ↦
    { hom := f M
      inv := g M
      hom_inv_id := by ext U x; rfl
      inv_hom_id := by ext U x; rfl }) (fun _ ↦ by ext U x; rfl)

section
attribute [local irreducible] smallModulesEquiv

private def comparisonChangeAdjunction (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (p : R ⟶ S) :
    reductionChange T p ⊣ reductionRestrict T p := by
  let e : reductionChange T p ≅ SheafOfModules.tensorFunctor p :=
    CompletedConstantAlgebra.functorIsoOfObjMap _ _
      ((reductionChangeExistence T p).choose_spec.choose)
      (fun f ↦ (reductionChangeExistence T p).choose_spec.choose_spec.choose f)
  exact (SheafOfModules.tensorAdjunction p).ofNatIsoLeft e.symm

private def smallChangeAdjunction (T : Scheme.{t})
    {B H : Sheaf (comparisonTopology T) CommRingCat.{t + 1}} (q : B ⟶ H) :
    ConstantCompletion.change q ⊣ ConstantCompletion.res q := by
  let e : ConstantCompletion.change q ≅ SheafOfModules.tensorFunctor q := Iso.refl _
  exact (SheafOfModules.tensorAdjunction q).ofNatIsoLeft e.symm

private theorem comparisonTensorUnit_apply (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (p : R ⟶ S)
    (M : reductionModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((SheafOfModules.tensorAdjunction p).unit.app M).val.app U x =
      (toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf p M).presheaf).app U
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(p.hom.app U).hom] x) := by
  rfl

private theorem comparisonChangeUnit_apply (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (p : R ⟶ S)
    (M : reductionModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((comparisonChangeAdjunction T p).unit.app M).val.app U x =
      reductionTensorSection T p M U 1 x := by
  dsimp only [comparisonChangeAdjunction, Adjunction.ofNatIsoLeft_unit,
    NatTrans.comp_app, CategoryTheory.Functor.whiskerRight_app]
  change (eqToHom ((reductionChangeExistence T p).choose_spec.choose M).symm).val.app U
      (((SheafOfModules.tensorAdjunction p).unit.app M).val.app U x) = _
  exact congrArg
    (fun z ↦ (eqToHom ((reductionChangeExistence T p).choose_spec.choose M).symm).val.app U z)
    (comparisonTensorUnit_apply T p M U x)

private theorem smallChangeUnit_apply (T : Scheme.{t})
    {B H : Sheaf (comparisonTopology T) CommRingCat.{t + 1}} (q : B ⟶ H)
    (M : ConstantCompletion.Mod B) (U : (CechConstantAlgebra.smallSite T)ᵒᵖ)
    (x : M.val.obj U) :
    ((smallChangeAdjunction T q).unit.app M).val.app U x =
      ConstantCompletion.tensorSection q M U 1 x := by
  rfl

private theorem tensorRestriction_hom_ext (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (p : R ⟶ S)
    (hp : ∀ U, Function.Surjective (p.hom.app U))
    (M N : reductionModules T R)
    (f g : (reductionRestrict T p).obj ((SheafOfModules.tensorFunctor p).obj M) ⟶ N)
    (h : ∀ (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      f.val.app U ((toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf p M).presheaf).app U
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(p.hom.app U).hom] x)) =
      g.val.app U ((toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf p M).presheaf).app U
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(p.hom.app U).hom] x))) : f = g := by
  apply (SheafOfModules.toSheaf (reductionModuleRing T R)).map_injective
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology T) _ _ N.isSheaf
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext z
  change f.val.app U ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf p M).presheaf).app U z) =
    g.val.app U ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf p M).presheaf).app U z)
  let : Module (R.obj.obj U) (S.obj.obj U) := Module.compHom _ (p.hom.app U).hom
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
    obtain ⟨r, rfl⟩ := hp U s
    have he : (p.hom.app U r) ⊗ₜ[R.obj.obj U,(p.hom.app U).hom] x =
        (1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(p.hom.app U).hom] (r • x) := by
      have ht := TensorProduct.smul_tmul (R := R.obj.obj U) r (1 : S.obj.obj U) x
      change ((p.hom.app U).hom r * 1) ⊗ₜ[R.obj.obj U,(p.hom.app U).hom] x =
        (1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(p.hom.app U).hom] (r • x) at ht
      simpa only [mul_one] using ht
    rw [he]
    exact h U (r • x)
  | add x y hx hy => simp only [map_add, hx, hy]

attribute [local irreducible] comparisonChangeAdjunction smallChangeAdjunction

private theorem comparisonChangeUnit_epi (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (p : R ⟶ S)
    (hp : ∀ U, Function.Surjective (p.hom.app U)) (M : reductionModules T R) :
    Epi ((comparisonChangeAdjunction T p).unit.app M) := by
  constructor
  intro N f g hfg
  let e : (SheafOfModules.tensorFunctor p).obj M ≅ (reductionChange T p).obj M :=
    eqToIso ((reductionChangeExistence T p).choose_spec.choose M).symm
  let k := (reductionRestrict T p).mapIso e
  apply (cancel_epi k.hom).mp
  apply tensorRestriction_hom_ext T p hp M N (k.hom ≫ f) (k.hom ≫ g)
  intro U x
  have h := congrArg (fun z ↦ z.val.app U x) hfg
  change f.val.app U (((comparisonChangeAdjunction T p).unit.app M).val.app U x) =
    g.val.app U (((comparisonChangeAdjunction T p).unit.app M).val.app U x) at h
  erw [comparisonChangeUnit_apply] at h
  exact h

attribute [local irreducible] smallRestrictionComparison

section Transport
variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂]
  [Category* D₁] [Category* D₂]
  (E : C₁ ≌ C₂) (G : D₁ ≌ D₂) (L : C₁ ⥤ D₁) (U : D₁ ⥤ C₁)
  (Q : C₂ ⥤ D₂) (V : D₂ ⥤ C₂) (adj : L ⊣ U) (adj' : Q ⊣ V)
  (h : G.inverse ⋙ U ≅ V ⋙ E.inverse)

private def restrictionTransport : U ⋙ E.functor ≅ G.functor ⋙ V :=
  (U ⋙ E.functor).leftUnitor.symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight G.unitIso (U ⋙ E.functor) ≪≫
    CategoryTheory.Functor.associator G.functor G.inverse (U ⋙ E.functor) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft G.functor
      ((CategoryTheory.Functor.associator G.inverse U E.functor).symm ≪≫
        CategoryTheory.Functor.isoWhiskerRight h E.functor ≪≫
        CategoryTheory.Functor.associator V E.inverse E.functor ≪≫
        CategoryTheory.Functor.isoWhiskerLeft V E.counitIso ≪≫ V.rightUnitor)

private def extensionTransport : L ⋙ G.functor ≅ E.functor ⋙ Q :=
  ((adj.comp G.toAdjunction).ofNatIsoRight h).leftAdjointUniq
    (E.toAdjunction.comp adj')

private def reductionTransport : (L ⋙ U) ⋙ E.functor ≅ E.functor ⋙ (Q ⋙ V) :=
  CategoryTheory.Functor.associator _ _ _ ≪≫
    CategoryTheory.Functor.isoWhiskerLeft _ (restrictionTransport E G U V h) ≪≫
    (CategoryTheory.Functor.associator _ _ _).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight (extensionTransport E G L U Q V adj adj' h) _ ≪≫
    CategoryTheory.Functor.associator _ _ _

private theorem reductionTransport_unit (M : C₁) :
    E.functor.map (adj.unit.app M) ≫
        (reductionTransport E G L U Q V adj adj' h).hom.app M =
      adj'.unit.app (E.functor.obj M) := by
  let adj₁ := (adj.comp G.toAdjunction).ofNatIsoRight h
  let adj₂ := E.toAdjunction.comp adj'
  let α := adj₁.leftAdjointUniq adj₂
  let η := adj.unit.app M
  let θ := adj'.unit.app (E.functor.obj M)
  have hu := Adjunction.unit_leftAdjointUniq_hom_app adj₁ adj₂ M
  simp only [adj₁, adj₂, Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app,
    NatTrans.comp_app, CategoryTheory.Functor.whiskerLeft_app, Category.assoc] at hu
  change η ≫ U.map (G.unitIso.hom.app (L.obj M)) ≫
      h.hom.app (G.functor.obj (L.obj M)) ≫ E.inverse.map (V.map (α.hom.app M)) =
    E.unitIso.hom.app M ≫ E.inverse.map θ at hu
  simp only [reductionTransport, restrictionTransport, extensionTransport,
    Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.isoWhiskerLeft_hom,
    CategoryTheory.Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.whiskerRight_app,
    CategoryTheory.Functor.associator_hom_app, CategoryTheory.Functor.associator_inv_app,
    CategoryTheory.Functor.leftUnitor_inv_app, CategoryTheory.Functor.rightUnitor_hom_app,
    Category.id_comp, Category.comp_id, Category.assoc,
    CategoryTheory.Functor.comp_map]
  erw [Category.id_comp]
  change E.functor.map η ≫
    E.functor.map (U.map (G.unitIso.hom.app (L.obj M))) ≫
      E.functor.map (h.hom.app (G.functor.obj (L.obj M))) ≫
        E.counitIso.hom.app (V.obj (G.functor.obj (L.obj M))) ≫
          V.map (α.hom.app M) = θ
  have hn := E.counitIso.hom.naturality (V.map (α.hom.app M))
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] at hn
  calc
    _ = E.functor.map (η ≫ U.map (G.unitIso.hom.app (L.obj M)) ≫
          h.hom.app (G.functor.obj (L.obj M)) ≫ E.inverse.map (V.map (α.hom.app M))) ≫
        E.counitIso.hom.app (V.obj (Q.obj (E.functor.obj M))) := by
      simp only [E.functor.map_comp, Category.assoc]
      erw [← hn]
      rfl
    _ = E.functor.map (E.unitIso.hom.app M ≫ E.inverse.map θ) ≫
        E.counitIso.hom.app (V.obj (Q.obj (E.functor.obj M))) := by rw [hu]
    _ = θ := by
      rw [E.functor.map_comp, Category.assoc]
      erw [E.counitIso.hom.naturality θ]
      dsimp only [CategoryTheory.Functor.id_obj, CategoryTheory.Functor.id_map]
      rw [← Category.assoc, E.functor_unitIso_comp, Category.id_comp]
end Transport

attribute [local irreducible] restrictionTransport extensionTransport reductionTransport

private def smallReductionComparison (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {B H : Sheaf (comparisonTopology T) CommRingCat.{t + 1}}
    (β : (CechConstantAlgebra.pushRing T).obj R ≅ B)
    (δ : (CechConstantAlgebra.pushRing T).obj S ≅ H)
    (p : R ⟶ S) (q : B ⟶ H)
    (hp : β.hom ≫ q = (CechConstantAlgebra.pushRing T).map p ≫ δ.hom) :
    (reductionChange T p ⋙ reductionRestrict T p) ⋙
        (smallModulesEquiv T R B β).functor ≅
      (smallModulesEquiv T R B β).functor ⋙
        (ConstantCompletion.change q ⋙ ConstantCompletion.res q) :=
  reductionTransport (smallModulesEquiv T R B β) (smallModulesEquiv T S H δ)
    (reductionChange T p) (reductionRestrict T p)
    (ConstantCompletion.change q) (ConstantCompletion.res q)
    (comparisonChangeAdjunction T p) (smallChangeAdjunction T q)
    (smallRestrictionComparison T β δ p q hp)

private theorem smallReductionComparison_unit (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {B H : Sheaf (comparisonTopology T) CommRingCat.{t + 1}}
    (β : (CechConstantAlgebra.pushRing T).obj R ≅ B)
    (δ : (CechConstantAlgebra.pushRing T).obj S ≅ H)
    (p : R ⟶ S) (q : B ⟶ H)
    (hp : β.hom ≫ q = (CechConstantAlgebra.pushRing T).map p ≫ δ.hom)
    (M : reductionModules T R) :
    (smallModulesEquiv T R B β).functor.map ((comparisonChangeAdjunction T p).unit.app M) ≫
        (smallReductionComparison T β δ p q hp).hom.app M =
      (smallChangeAdjunction T q).unit.app ((smallModulesEquiv T R B β).functor.obj M) :=
  reductionTransport_unit _ _ _ _ _ _ _ _ _ M

attribute [local irreducible] smallReductionComparison

private def comparisonModulesEquiv (T : Scheme.{t}) {A : Type (t + 1)}
    [CommRing A] (d : AdicCoefficientDatum A) :
    reductionModules T (d.completedRing T) ≌ ConstantCompletion.Mod (comparisonRing T d) :=
  smallModulesEquiv T (d.completedRing T) (comparisonRing T d)
    (CechConstantAlgebra.algebraIso T d.ideal (pbcCompletedComparison T d))

private instance comparisonModulesEquiv_additive (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (comparisonModulesEquiv T d).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

private theorem completedProjection_comparison (T : Scheme.{t}) {A : Type (t + 1)}
    [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    completedReductionProjection T d n = (pbcCompletedComparison T d).inv ≫
      limit.π (adicLisseRingSystem T d.ideal) (op n) ≫
        (pbcLevelConstantComparison T d n).hom := by
  apply (cancel_epi (pbcCompletedComparison T d).hom).mp
  dsimp only [pbcCompletedComparison, HasLimit.isoOfNatIso, completedReductionProjection]
  erw [Iso.hom_inv_id_assoc]
  exact limMap_π (pbcConstantSystemComparison T d).hom (op n)

private theorem comparisonRing_projection (T : Scheme.{t}) {A : Type (t + 1)}
    [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (CechConstantAlgebra.algebraIso T d.ideal (pbcCompletedComparison T d)).hom ≫
        ConstantCompletion.projection (comparisonTopology T) A d.ideal n =
      (CechConstantAlgebra.pushRing T).map (completedReductionProjection T d n) ≫
        (CechConstantAlgebra.pushRing T).map (pbcLevelConstantComparison T d n).inv ≫
          (CechConstantAlgebra.constantsIso T).hom.app
            (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))) :=
  CechConstantAlgebra.projection_transport T d.ideal (pbcCompletedComparison T d) n
    (pbcLevelConstantComparison T d n) (completedReductionProjection T d n)
    (completedProjection_comparison T d n)

private def comparisonFiniteRing (T : Scheme.{t}) {A : Type (t + 1)}
    [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (CechConstantAlgebra.pushRing T).obj (reductionCoefficient T d n) ≅
      ConstantCompletion.finite (comparisonTopology T) A d.ideal n :=
  (CechConstantAlgebra.pushRing T).mapIso (pbcLevelConstantComparison T d n).symm ≪≫
    (CechConstantAlgebra.constantsIso T).app
      (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))

private def comparisonFiniteReduction (T : Scheme.{t}) {A : Type (t + 1)}
    [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    completedReductionLevel T d n ⋙ (comparisonModulesEquiv T d).functor ≅
      (comparisonModulesEquiv T d).functor ⋙
        ConstantCompletion.reduction (comparisonTopology T) A d.ideal true n :=
  smallReductionComparison T
    (CechConstantAlgebra.algebraIso T d.ideal (pbcCompletedComparison T d))
    (comparisonFiniteRing T d n) (completedReductionProjection T d n)
    (ConstantCompletion.projection (comparisonTopology T) A d.ideal n)
    (comparisonRing_projection T d n)

private theorem completedProjection_surjective (T : Scheme.{t}) {A : Type (t + 1)}
    [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) (U : T.ProEtᵒᵖ) :
    Function.Surjective ((completedReductionProjection T d n).hom.app U) := by
  let := d.noetherian
  let e := pbcCompletedComparison T d
  exact CechConstantAlgebra.projection_surjective T d.ideal e
    n (pbcLevelConstantComparison T d n) (completedReductionProjection T d n)
    (completedProjection_comparison T d n) U

private theorem actualReductionUnit_component (T : Scheme.{t}) {A : Type (t + 1)}
    [CommRing A] (d : AdicCoefficientDatum A) (M : reductionModules T (d.completedRing T))
    (n : ℕ) :
    ((completedReductionModuleUnit d T).app M).app (op n) =
      (comparisonChangeAdjunction T (completedReductionProjection T d n)).unit.app M := by
  ext U x
  exact ((completedReductionModuleUnit_exists d T).exists.choose_spec M n U x).trans
    (comparisonChangeUnit_apply T (completedReductionProjection T d n) M U x).symm

private theorem constantReductionUnit_component (T : Scheme.{t}) {A : Type (t + 1)}
    [CommRing A] (d : AdicCoefficientDatum A) (M : ConstantCompletion.Mod (comparisonRing T d))
    (n : ℕ) :
    ((ConstantCompletion.reductionUnit (comparisonTopology T) A d.ideal true).app M).app
        (op n) =
      (smallChangeAdjunction T
        (ConstantCompletion.projection (comparisonTopology T) A d.ideal n)).unit.app M := by
  ext U x
  exact ((ConstantCompletion.reductionUnit_existsUnique
    (comparisonTopology T) A d.ideal true).exists.choose_spec M n U x).trans
      (smallChangeUnit_apply T
        (ConstantCompletion.projection (comparisonTopology T) A d.ideal n) M U x).symm

private theorem comparisonFiniteReduction_unit (T : Scheme.{t}) {A : Type (t + 1)}
    [CommRing A] (d : AdicCoefficientDatum A) (M : reductionModules T (d.completedRing T))
    (n : ℕ) :
    (comparisonModulesEquiv T d).functor.map
          (((completedReductionModuleUnit d T).app M).app (op n)) ≫
        (comparisonFiniteReduction T d n).hom.app M =
      ((ConstantCompletion.reductionUnit (comparisonTopology T) A d.ideal true).app
        ((comparisonModulesEquiv T d).functor.obj M)).app (op n) := by
  rw [actualReductionUnit_component, constantReductionUnit_component]
  exact smallReductionComparison_unit T _ _ _ _ (comparisonRing_projection T d n) M

private theorem comparisonFiniteReduction_step (T : Scheme.{t}) {A : Type (t + 1)}
    [CommRing A] (d : AdicCoefficientDatum A) (M : reductionModules T (d.completedRing T))
    (n : ℕ) :
    (comparisonModulesEquiv T d).functor.map
        (((completedReductionModuleTowerFunctor T d).obj M).map
          (homOfLE (Nat.le_succ n)).op) ≫
      (comparisonFiniteReduction T d n).hom.app M =
    (comparisonFiniteReduction T d (n + 1)).hom.app M ≫
      ((ConstantCompletion.reductionTower (comparisonTopology T) A d.ideal true).obj
        ((comparisonModulesEquiv T d).functor.obj M)).map
          (homOfLE (Nat.le_succ n)).op := by
  let E := comparisonModulesEquiv T d
  let τ := (completedReductionModuleUnit d T).app M
  let σ := (ConstantCompletion.reductionUnit (comparisonTopology T) A d.ideal true).app
    (E.functor.obj M)
  have : Epi (τ.app (op (n + 1))) := by
    rw [show τ.app (op (n + 1)) =
      (comparisonChangeAdjunction T (completedReductionProjection T d (n + 1))).unit.app M
      from actualReductionUnit_component T d M (n + 1)]
    exact comparisonChangeUnit_epi T _ (completedProjection_surjective T d (n + 1)) M
  have : Epi (E.functor.map (τ.app (op (n + 1)))) := inferInstance
  apply (cancel_epi (E.functor.map (τ.app (op (n + 1))))).mp
  have hτ := τ.naturality (homOfLE (Nat.le_succ n)).op
  have hσ := σ.naturality (homOfLE (Nat.le_succ n)).op
  dsimp only [CategoryTheory.Functor.const_obj_map] at hτ hσ
  erw [Category.id_comp] at hτ hσ
  change E.functor.map (τ.app (op (n + 1))) ≫ E.functor.map _ ≫ _ = _
  rw [← E.functor.map_comp_assoc, ← hτ, comparisonFiniteReduction_unit]
  rw [← Category.assoc, comparisonFiniteReduction_unit]
  exact hσ

private def comparisonReductionModuleTowers (T : Scheme.{t}) {A : Type (t + 1)}
    [CommRing A] (d : AdicCoefficientDatum A) :
    completedReductionModuleTowerFunctor T d ⋙
        (CategoryTheory.Functor.whiskeringRight ℕᵒᵖ _ _).obj
          (comparisonModulesEquiv T d).functor ≅
      (comparisonModulesEquiv T d).functor ⋙
        ConstantCompletion.reductionTower (comparisonTopology T) A d.ideal true := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let η := NatTrans.ofOpSequence
      (F := (completedReductionModuleTowerFunctor T d).obj M ⋙
        (comparisonModulesEquiv T d).functor)
      (G := (ConstantCompletion.reductionTower (comparisonTopology T) A d.ideal true).obj
        ((comparisonModulesEquiv T d).functor.obj M))
      (fun n ↦ (comparisonFiniteReduction T d n).hom.app M)
      (fun n ↦ comparisonFiniteReduction_step T d M n)
    exact NatIso.ofComponents (fun n ↦ (comparisonFiniteReduction T d n.unop).app M)
      (fun f ↦ η.naturality f)
  · intro M N f
    apply NatTrans.ext
    funext n
    exact (comparisonFiniteReduction T d n.unop).hom.naturality f

private theorem comparisonReductionModuleTowers_component (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : reductionModules T (d.completedRing T)) (n : ℕ) :
    ((comparisonReductionModuleTowers T d).hom.app M).app (op n) =
      (comparisonFiniteReduction T d n).hom.app M := rfl

end
section
private def comparisonModulesEquiv_to_cech
    (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (comparisonModulesEquiv T d).functor ≅ (completedCechModulesEquiv T d).functor ⋙
      ConstantCompletion.res
        (CechConstantAlgebra.algebraIso T d.ideal (pbcCompletedComparison T d)).inv := by
  let F := (comparisonModulesEquiv T d).functor
  let G := (completedCechModulesEquiv T d).functor ⋙ ConstantCompletion.res
    (CechConstantAlgebra.algebraIso T d.ideal (pbcCompletedComparison T d)).inv
  let f (M : reductionModules T (d.completedRing T)) : F.obj M ⟶ G.obj M :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
        (X := (F.obj M).val.obj U) (Y := (G.obj M).val.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
       naturality := fun _ ↦ by ext x; rfl }⟩
  let g (M : reductionModules T (d.completedRing T)) : G.obj M ⟶ F.obj M :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
        (X := (G.obj M).val.obj U) (Y := (F.obj M).val.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
       naturality := fun _ ↦ by ext x; rfl }⟩
  exact NatIso.ofComponents (fun M ↦
    { hom := f M
      inv := g M
      hom_inv_id := by ext U x; rfl
      inv_hom_id := by ext U x; rfl }) (fun _ ↦ by ext U x; rfl)
end

private def comparisonCompletedRingIso
    (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    completedCechRing T d ≅
      ConstantCompletion.coefficients (completedCechTopology T) A d.ideal true :=
  CechConstantAlgebra.algebraIso T d.ideal (pbcCompletedComparison T d)

private theorem comparisonCompletedRingIso_scalar
    (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : (completedCechSite T)ᵒᵖ) (x : A) :
    (comparisonCompletedRingIso T d).hom.hom.app U ((completedCechScalar T d x).val U) =
      (ConstantCompletion.algebraSection
        (ConstantCompletion.coefficientMap (completedCechTopology T) A d.ideal) x).val U := by
  let c := adicDatumScalar T (intrinsicPresentationDatum d) ≫ (pbcCompletedComparison T d).hom
  have hc : ∀ n : ℕ, c ≫ (pbcCompletedComparison T d).inv ≫
      limit.π (adicLisseRingSystem T d.ideal) (op n) =
        (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) := by
    intro n
    dsimp only [c]
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact (adicDatumScalar_exists T (intrinsicPresentationDatum d)).exists.choose_spec n
  have h := CechConstantAlgebra.algebraIso_scalar T d.ideal
    (pbcCompletedComparison T d) c hc
  have h' := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app U) h)
      ((adicLisseConstantUnit T A).app (AsSmall.down.op.obj U) x)
  change (comparisonCompletedRingIso T d).hom.hom.app U
    ((completedCechScalar T d x).val U) =
      (ConstantCompletion.coefficientMap (completedCechTopology T) A d.ideal).hom.app U
        (((CechConstantAlgebra.constantsIso T).hom.app (CommRingCat.of A)).hom.app U
          ((adicLisseConstantUnit T A).app (AsSmall.down.op.obj U) x)) at h'
  rw [CechConstantAlgebra.constantsIso_unit] at h'
  exact h'

/-- The constants-to-functions equivalence identifies the completed ring, its scalars,
its module category and every positive quotient, including their strict quotient units.

Source: Stacks Tags 03CR, 093M and 06YY.
(blueprint: lem-weil-pbc-completed-constant-coefficient-equivalence).

Proof: sheafification commutes with the canonical equivalence to the small site.
The constants maps identify finite quotient rings and commute with their transitions;
the induced limit isomorphism identifies the completed rings. Its composite with the
coefficient map has the same finite projections, so it preserves every scalar. The
ringed-site equivalence gives the module equivalence. Adjunction uniqueness identifies
scalar extension at every finite quotient. Its unit is the tensor insertion, hence
agrees with the strict quotient unit. Surjectivity of each quotient makes these units
epimorphisms, and cancelling them proves compatibility with all quotient transitions. -/
theorem completed_constant_coefficient_equivalence
    (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ∃ β : completedCechRing T d ≅
        ConstantCompletion.coefficients (completedCechTopology T) A d.ideal true,
      (∀ (U : (completedCechSite T)ᵒᵖ) (x : A),
        β.hom.hom.app U ((completedCechScalar T d x).val U) =
          (ConstantCompletion.algebraSection
            (ConstantCompletion.coefficientMap (completedCechTopology T) A d.ideal) x).val U) ∧
      ∃ E : reductionModules T (d.completedRing T) ≌ ConstantCompletion.Mod
          (ConstantCompletion.coefficients (completedCechTopology T) A d.ideal true),
        E.functor.Additive ∧
        Nonempty (E.functor ≅ (completedCechModulesEquiv T d).functor ⋙
          ConstantCompletion.res β.inv) ∧
        ∃ η : completedReductionModuleTowerFunctor T d ⋙
            (CategoryTheory.Functor.whiskeringRight ℕᵒᵖ _ _).obj E.functor ≅
              E.functor ⋙ ConstantCompletion.reductionTower
                (completedCechTopology T) A d.ideal true,
          ∀ (M : reductionModules T (d.completedRing T)) (n : ℕ),
            E.functor.map (((completedReductionModuleUnit d T).app M).app (op n)) ≫
                (η.hom.app M).app (op n) =
              ((ConstantCompletion.reductionUnit
                (completedCechTopology T) A d.ideal true).app (E.functor.obj M)).app (op n) := by
  refine ⟨comparisonCompletedRingIso T d, comparisonCompletedRingIso_scalar T d,
    comparisonModulesEquiv T d, comparisonModulesEquiv_additive T d,
    ⟨comparisonModulesEquiv_to_cech T d⟩,
    comparisonReductionModuleTowers T d, ?_⟩
  intro M n
  rw [comparisonReductionModuleTowers_component]
  exact comparisonFiniteReduction_unit T d M n

end AlgebraicGeometry.Scheme
