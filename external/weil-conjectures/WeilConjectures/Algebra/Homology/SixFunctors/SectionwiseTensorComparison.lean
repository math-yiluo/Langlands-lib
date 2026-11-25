/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.CategoryTheory.RingedCocontinuousMonoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import all Mathlib.CategoryTheory.Localization.Monoidal.Functor
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-! # Section-normalized tensor comparison for module restriction

Source: Stacks Project, Tags 03EK and 04B8.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] SheafOfModules.monoidalCategory
universe c v d z w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace SheafOfModules
variable {C : Type c} [Category.{v} C] {D : Type d} [Category.{z} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

-- Section evaluation crosses both coefficient-ring and sheafification presentations.
/-- Module restriction along a continuous and cocontinuous functor with invertible
coefficient map commutes with the ordinary tensor, naturally in both factors and
with the identity formula on pure sections.
Source: Stacks Project Tags 03EK and 04B8
(blueprint: lem-sf-sectionwise-tensor-comparison).

Proof: use the balanced presheaf tensor comparison for the invertible scalar map,
then commute restriction with sheafification. Naturality of the sheafification unit
computes the inverse comparison on pure tensors, and cancellation gives the forward
formula. Maps out of a sheafified tensor are determined by these sections, so their
formula also proves naturality in both factors. No nonzero ring, point or boundedness
hypothesis is used. -/
theorem sectionwiseTensorComparison
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf J CommRingCat.{w}) (S : Sheaf K CommRingCat.{w})
    (a : (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R ≅
      (f.sheafPushforwardContinuous RingCat.{w} J K).obj
        ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S)) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients S
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory S
    letI := SheafOfModules.monoidalCategory R
    let U := SheafOfModules.pushforward.{w} a.hom
    ∃ e : ∀ M N : scalarModules K S, U.obj (M ⊗ N) ≅ U.obj M ⊗ U.obj N,
      (∀ {M M' N N'} (f : M ⟶ M') (h : N ⟶ N'),
        U.map (f ⊗ₘ h) ≫ (e M' N').hom =
          (e M N).hom ≫ (U.map f ⊗ₘ U.map h)) ∧
      ∀ (M N : scalarModules K S) (V : Cᵒᵖ)
        (x : M.val.obj (f.op.obj V))
        (y : N.val.obj (f.op.obj V)),
        (e M N).hom.val.app V
          (SheafOfModules.ScalarHomOrdinary.pure S M N
            (f.op.obj V) x y) =
        SheafOfModules.ScalarHomOrdinary.pure R (U.obj M) (U.obj N) V x y := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.monoidalCategory R
  let U := SheafOfModules.pushforward.{w} a.hom
  let : MonoidalCategory (PresheafOfModules.{w}
      ((sheafCompose K
        (forget₂ CommRingCat.{w} RingCat.{w})).obj S).obj) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModules.{w}
      (S.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})))
  let : MonoidalCategory (PresheafOfModules.{w}
      ((sheafCompose J
        (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModules.{w}
      (R.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})))
  let P : PresheafOfModules.{w}
      ((sheafCompose K
        (forget₂ CommRingCat.{w} RingCat.{w})).obj S).obj ⥤
      PresheafOfModules.{w} ((sheafCompose J
        (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj :=
    PresheafOfModules.pushforward.{w} (F := f) a.hom.hom
  let sh := PresheafOfModules.sheafification.{w} (R :=
    (sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (𝟙 _)
  let : P.LaxMonoidal := PresheafOfModules.pushforwardLaxMonoidal a.hom.hom
  have hiso (M N : PresheafOfModules.{w}
      (S.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :
      IsIso (Functor.LaxMonoidal.μ P M N) := by
    apply SheafOfModules.presheaf_isIso
    intro V
    dsimp only [P]
    erw [PresheafOfModules.pushforward_μ_app a.hom.hom M N V]
    exact WeilConjectures.SemilinearSections.restrictScalars_mu_isIso
      (R.obj.obj V) (S.obj.obj (f.op.obj V)) (a.hom.hom.app V).hom _ _
      (ConcreteCategory.bijective_of_isIso (a.hom.hom.app V))
  let θ : P ⋙ sh ≅ PresheafOfModules.sheafification.{w} (R :=
      (sheafCompose K
        (forget₂ CommRingCat.{w} RingCat.{w})).obj S) (𝟙 _) ⋙ U :=
    SheafOfModules.restrictionSheafificationIso f R S a
  let e (M N : scalarModules K S) : U.obj (M ⊗ N) ≅ U.obj M ⊗ U.obj N :=
    U.mapIso (SheafOfModules.tensorObjIsoSheafification M N) ≪≫
      (θ.app (M.val ⊗ N.val)).symm ≪≫
      sh.mapIso (asIso (Functor.LaxMonoidal.μ P M.val N.val)).symm ≪≫
      (SheafOfModules.tensorObjIsoSheafification (U.obj M) (U.obj N)).symm
  have hinv (M N : scalarModules K S) (V : Cᵒᵖ)
      (x : M.val.obj (f.op.obj V)) (y : N.val.obj (f.op.obj V)) :
      (e M N).inv.val.app V
        (SheafOfModules.ScalarHomOrdinary.pure R (U.obj M) (U.obj N) V x y) =
      SheafOfModules.ScalarHomOrdinary.pure S M N (f.op.obj V) x y := by
    let η := PresheafOfModules.sheafificationAdjunction.{w} (R :=
      (sheafCompose J
        (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (𝟙 _)
    have hcancel := congrArg (fun h ↦ h.val.app V
      ((η.unit.app ((U.obj M).val ⊗ (U.obj N).val)).app V
        (x ⊗ₜ[R.obj.obj V] y)))
      (SheafOfModules.tensorObjIsoSheafification (U.obj M) (U.obj N)).inv_hom_id
    change (SheafOfModules.tensorObjIsoSheafification (U.obj M) (U.obj N)).hom.val.app V
      (SheafOfModules.ScalarHomOrdinary.pure R (U.obj M) (U.obj N) V x y) =
        _ at hcancel
    dsimp only [e, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    erw [hcancel]
    have hn := congrArg (fun h ↦ h.app V
      (x ⊗ₜ[R.obj.obj V] y))
      (η.unit.naturality (asIso (Functor.LaxMonoidal.μ P M.val N.val)).hom)
    change (η.unit.app _).app V
      ((asIso (Functor.LaxMonoidal.μ P M.val N.val)).hom.app V
        (x ⊗ₜ[R.obj.obj V] y)) =
      (sh.map (asIso (Functor.LaxMonoidal.μ P M.val N.val)).hom).val.app V _ at hn
    erw [← hn]
    change (U.map (SheafOfModules.tensorObjIsoSheafification M N).inv).val.app V
      ((θ.app (M.val ⊗ N.val)).hom.val.app V
        ((η.unit.app (P.obj (M.val ⊗ N.val))).app V
          ((Functor.LaxMonoidal.μ P M.val N.val).app V
            (x ⊗ₜ[R.obj.obj V] y)))) = _
    erw [PresheafOfModules.pushforward_μ_app_tmul
      (F := f) (R := S.obj) (S := R.obj)
      a.hom.hom M.val N.val V x y]
    erw [_root_.restrictionSheafificationMap_unit_apply
      a.hom (M.val ⊗ N.val) V (x ⊗ₜ[S.obj.obj (f.op.obj V)] y)]
    rfl
  have hgen (M N : scalarModules K S) (V : Cᵒᵖ)
      (x : M.val.obj (f.op.obj V)) (y : N.val.obj (f.op.obj V)) :
      (e M N).hom.val.app V
        (SheafOfModules.ScalarHomOrdinary.pure S M N (f.op.obj V) x y) =
      SheafOfModules.ScalarHomOrdinary.pure R (U.obj M) (U.obj N) V x y := by
    exact (congrArg ((e M N).hom.val.app V) (hinv M N V x y).symm).trans
      (congrArg (fun h ↦ h.val.app V
        (SheafOfModules.ScalarHomOrdinary.pure R (U.obj M) (U.obj N) V x y))
        (e M N).inv_hom_id)
  refine ⟨e, ?_, hgen⟩
  intro M M' N N' h k
  apply (cancel_epi (e M N).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply SheafOfModules.ScalarHomOrdinary.pure_hom_ext R (U.obj M) (U.obj N)
  intro V x y
  change M.val.obj (f.op.obj V) at x
  change N.val.obj (f.op.obj V) at y
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [hinv M N V x y]
  change (e M' N').hom.val.app V
    ((h ⊗ₘ k).val.app (f.op.obj V)
      (SheafOfModules.ScalarHomOrdinary.pure S M N (f.op.obj V) x y)) = _
  exact (congrArg ((e M' N').hom.val.app V)
      (SheafOfModules.ScalarHomOrdinary.pure_map S h k (f.op.obj V) x y)).trans
    ((hgen M' N' V (h.val.app (f.op.obj V) x) (k.val.app (f.op.obj V) y)).trans
      (SheafOfModules.ScalarHomOrdinary.pure_map R (U.map h) (U.map k) V x y).symm)

end SheafOfModules
