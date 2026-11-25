/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import all WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.Algebra.Homology.PoincareDuality.TensorTrilinearUniversal

/-! # Cancellation in the explicit site tensor presentation

Source: Stacks 03EK and 0B8N, tensor comparison and evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe uC vC r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max uC vC r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  [HasSheafify J AddCommGrpCat.{max uC vC r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  (R : Sheaf J CommRingCat.{max uC vC r})
attribute [local instance 2000] cochainModulesMonoidal

private def tensorToSite (N : LineEvaluation.Modules.{uC, vC, r} R) :
    tensorRight N ≅ siteSheafTensorRight.{vC, uC, max uC vC r, max uC vC r} (A :=
      R) N :=
  NatIso.ofComponents
    (fun M ↦ ScalarHomOrdinary.tensorIsoSite.{uC, vC, max uC vC r} _ M N)
    (by
      intro M M' f
      apply LineEvaluation.pure_hom_ext.{uC, vC, r}
        (R)
      intro U x y
      have hf := LineEvaluation.pure_map.{uC, vC, r}
        (R) f (𝟙 N) U x y
      rw [tensorHom_id] at hf
      change (ScalarHomOrdinary.tensorIsoSite.{uC, vC, max uC vC r} _ M' N).hom.val.app U
          (((tensorRight N).map f).val.app U
            (LineEvaluation.pureTensor.{uC, vC, r} _ M N U x y)) =
        ((siteSheafTensorRight.{vC, uC, max uC vC r, max uC vC r} N).map f).val.app U
          ((ScalarHomOrdinary.tensorIsoSite.{uC, vC, max uC vC r} _ M N).hom.val.app U
            (LineEvaluation.pureTensor.{uC, vC, r} _ M N U x y))
      have hf' : ((tensorRight N).map f).val.app U
          (LineEvaluation.pureTensor.{uC, vC, r} _ M N U x y) =
          LineEvaluation.pureTensor.{uC, vC, r} _ M' N U (f.val.app U x) y := by
        simpa only [tensorRight, curriedTensor, Functor.flip, id_val,
          PresheafOfModules.id_app, ModuleCat.id_apply]
          using hf
      exact (congrArg
        ((ScalarHomOrdinary.tensorIsoSite _ M' N).hom.val.app U) hf').trans
        ((ScalarHomOrdinary.tensorIsoSite_pure _ M' N U
          (f.val.app U x) y).trans
          ((congrArg (((siteSheafTensorRight N).map f).val.app U)
            (ScalarHomOrdinary.tensorIsoSite_pure _ M N U x y)).trans
            (map_tmul_first _ f U x y)).symm))

private def siteCancel (P Q : LineEvaluation.Modules.{uC, vC, r} R)
    (e : P ⊗ Q ≅ unit
      ((sheafCompose (J)
        (forget₂ CommRingCat RingCat)).obj (R))) :
    siteSheafTensorRight.{vC, uC, max uC vC r, max uC vC r} P ⋙
      siteSheafTensorRight.{vC, uC, max uC vC r, max uC vC r} Q ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (tensorToSite R P).symm
      (siteSheafTensorRight.{vC, uC, max uC vC r, max uC vC r} Q) ≪≫
    Functor.isoWhiskerLeft (tensorRight P) (tensorToSite R Q).symm ≪≫
      LineEvaluation.cancellation.{uC, vC, r}
        (R) P Q e

private theorem siteCancel_pure (P Q M : LineEvaluation.Modules.{uC, vC, r} R)
    (e : P ⊗ Q ≅ unit
      ((sheafCompose (J)
        (forget₂ CommRingCat RingCat)).obj (R)))
    (U : Cᵒᵖ) (x : M.val.obj U) (p : P.val.obj U) (q : Q.val.obj U) :
    ((siteCancel R P Q e).hom.app M).val.app U
      (siteSheafTensorTmul.{uC, vC, max uC vC r, max uC vC r} _ Q U
        (siteSheafTensorTmul.{uC, vC, max uC vC r, max uC vC r} M P U x p) q) =
      @SMul.smul _ _ (M.val.obj U).isModule.toSMul
        (e.hom.val.app U
          (LineEvaluation.pureTensor.{uC, vC, r} _ P Q U p q)) x := by
  change ((LineEvaluation.cancellation.{uC, vC, r}
      (R) P Q e).hom.app M).val.app U
    ((ScalarHomOrdinary.tensorIsoSite.{uC, vC, max uC vC r} _ (M ⊗ P) Q).inv.val.app U
      (((siteSheafTensorRight.{vC, uC, max uC vC r, max uC vC r} Q).map
        (ScalarHomOrdinary.tensorIsoSite.{uC, vC, max uC vC r} _ M P).inv).val.app U
          (siteSheafTensorTmul.{uC, vC, max uC vC r, max uC vC r} _ Q U
            (siteSheafTensorTmul.{uC, vC, max uC vC r, max uC vC r} M P U x p) q))) = _
  have h₁ := map_tmul_first
    (R)
    (ScalarHomOrdinary.tensorIsoSite _ M P).inv U
    (siteSheafTensorTmul M P U x p) q
  have h₂ := ScalarHomOrdinary.tensorIsoSite_inv_pure
    (R) (M ⊗ P) Q U
    ((ScalarHomOrdinary.tensorIsoSite _ M P).inv.val.app U
      (siteSheafTensorTmul M P U x p)) q
  have h₃ := ScalarHomOrdinary.tensorIsoSite_inv_pure
    (R) M P U x p
  exact (congrArg (fun z ↦
    ((LineEvaluation.cancellation.{uC, vC, r} _ P Q e).hom.app M).val.app U
      ((ScalarHomOrdinary.tensorIsoSite _ (M ⊗ P) Q).inv.val.app U z))
    h₁).trans ((congrArg
      (((LineEvaluation.cancellation.{uC, vC, r} _ P Q e).hom.app M).val.app U)
      h₂).trans ((congrArg (fun z ↦
        ((LineEvaluation.cancellation.{uC, vC, r} _ P Q e).hom.app M).val.app U
          (LineEvaluation.pureTensor.{uC, vC, r} _ (M ⊗ P) Q U z q)) h₃).trans
            (LineEvaluation.cancellation_pure.{uC, vC, r} _ P Q M e U x p q)))

attribute [local irreducible] tensorToSite siteCancel
/-- A specified evaluation pairing gives the unique cancellation on pure site tensors.
Source: Stacks 03EK and 0B8N
(blueprint: lem-pur-site-tensor-cancellation).
Proof: compare the explicit site tensor with the monoidal sheaf tensor. Transport
reassociation, the specified pairing and the unitor through that comparison. Its
formula follows on pure sections from the comparison formulas. The trilinear
universal property shows that this formula determines every component uniquely. -/
theorem siteTensorCancellation (P Q : LineEvaluation.Modules.{uC, vC, r} R)
    (e : P ⊗ Q ≅ unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ∃! c : siteSheafTensorRight P ⋙ siteSheafTensorRight Q ≅ 𝟭 _,
      ∀ (M : LineEvaluation.Modules.{uC, vC, r} R) (U : Cᵒᵖ)
        (x : M.val.obj U) (p : P.val.obj U) (q : Q.val.obj U),
        (c.hom.app M).val.app U
          (siteSheafTensorTmul _ Q U (siteSheafTensorTmul M P U x p) q) =
          @SMul.smul _ _ (M.val.obj U).isModule.toSMul
            (e.hom.val.app U (LineEvaluation.pureTensor R P Q U p q)) x := by
  let c := siteCancel R P Q e
  have hc := siteCancel_pure R P Q
  refine ⟨c, fun M U x p q ↦ hc M e U x p q, ?_⟩
  intro c' hc'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  obtain ⟨_, _, _, hext⟩ := tensor_trilinear_universal R
  apply (hext M P Q M (c'.hom.app M) (c.hom.app M)).2
  intro U x p q
  exact (hc' M U x p q).trans (hc M e U x p q).symm


end SheafOfModules
