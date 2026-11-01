import Langlands.Algebra.NonUnitalModuleAdmissibilityReflexivityProof
import Langlands.Algebra.NonUnitalModuleDualRightExactnessProof

/-! Categorical simplicity argument for Renard I.5.1. -/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleAdmissibilitySimplicityProof

open CategoryTheory NonUnitalModuleDual NonUnitalModuleAdmissibilityStatements
open NonUnitalModuleBidualInjectionProof

universe uA uM vC vD uC uD

private theorem simple_of_contravariant_simple
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    (F : Cᵒᵖ ⥤ D) [F.Faithful] [F.PreservesZeroMorphisms]
    (hmono : ∀ {X Y : C} (f : X ⟶ Y), Mono f → Epi (F.map f.op))
    (X : C) [Simple (F.obj (Opposite.op X))] : Simple X := by
  refine ⟨fun {Y} f hf => ?_⟩
  constructor
  · intro hi hzero
    let _ := hi
    have hFzero : F.map f.op = 0 := by simp [hzero]
    let g := inv (F.map f.op)
    have hid : F.map f.op ≫ g = 𝟙 _ := IsIso.hom_inv_id (F.map f.op)
    rw [hFzero, Limits.zero_comp] at hid
    exact id_nonzero (F.obj (Opposite.op X)) hid.symm
  · intro hne
    let _ := hmono f hf
    have hFne : F.map f.op ≠ 0 := by
      intro hzero
      have hz : f.op = 0 := F.map_eq_zero_iff.mp hzero
      exact hne (by simpa using congrArg Quiver.Hom.unop hz)
    let _ := isIso_of_epi_of_nonzero hFne
    let _ : Mono f.op := F.mono_of_mono_map inferInstance
    let _ : Epi f := unop_epi_of_mono f.op
    exact isIso_of_mono_of_epi f

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  (hA : IsIdempotented A)

private theorem leftToRight_faithful :
    (leftToRightFunctor.{uA, uM} hA).Faithful where
  map_injective {X Y} f g h := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    apply eq_of_forall_dual_apply_eq hA X.unop.property
    intro φ
    exact congrArg (fun k => (NonUnitalModuleHom.toAddMonoidHom k.hom φ).val m) h

private theorem rightToLeft_faithful :
    (rightToLeftFunctor.{uA, uM} hA).Faithful where
  map_injective {X Y} f g h := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    apply eq_of_forall_dual_apply_eq hA.op X.unop.property
    intro φ
    exact congrArg (fun k => (NonUnitalModuleHom.toAddMonoidHom k.hom φ).val m) h

private theorem simple_of_dual_simple (M : NondegenerateModuleCat.{uA, uM} A)
    [hs : Simple (dualObject hA M)] : Simple M := by
  let _ := NondegenerateModuleCat.abelian.{uA, uM} A hA
  let _ := NondegenerateModuleCat.abelian.{uA, uM} Aᵐᵒᵖ hA.op
  let _ := leftToRight_faithful.{uA, uM} hA
  let _ := leftToRight_additive.{uA, uM} hA
  let _ : Simple ((leftToRightFunctor hA).obj (Opposite.op M)) := hs
  exact simple_of_contravariant_simple (leftToRightFunctor hA)
    (fun f hf => leftToRight_epi_of_mono hA f hf) M

private theorem simple_of_rightDual_simple
    (M : RightNondegenerateModuleCat.{uA, uM} A)
    [hs : Simple (rightDualObject hA M)] : Simple M := by
  let _ := NondegenerateModuleCat.abelian.{uA, uM} A hA
  let _ := NondegenerateModuleCat.abelian.{uA, uM} Aᵐᵒᵖ hA.op
  let _ := rightToLeft_faithful.{uA, uM} hA
  let _ := rightToLeft_additive.{uA, uM} hA
  let _ : Simple ((rightToLeftFunctor hA).obj (Opposite.op M)) := hs
  exact simple_of_contravariant_simple (rightToLeftFunctor hA)
    (fun f hf => rightToLeft_epi_of_mono hA f hf) M

variable {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hM : IsNondegenerate A M)

/-- Admissibility makes simplicity equivalent for the original module and actual dual. -/
theorem admissibleSimpleIffDualSimple : AdmissibleSimpleIffDualSimple hA hM := by
  intro hadm
  let X : NondegenerateModuleCat.{uA, uM} A := ⟨NonUnitalModuleCat.of A M, hM⟩
  change Simple X ↔ Simple (dualObject hA X)
  let _ := NondegenerateModuleCat.abelian.{uA, uM} A hA
  let _ := NondegenerateModuleCat.abelian.{uA, uM} Aᵐᵒᵖ hA.op
  constructor
  · intro hs
    let _ := hs
    let ev : X ⟶ (bidualFunctor hA).obj X := (evaluationNatTrans hA).app X
    have hb :=
      (NonUnitalModuleAdmissibilityReflexivityProof.admissibleIffEvaluationBijective hA hM).1
        hadm
    let _ : Mono ev := (NondegenerateModuleExactnessConcrete.mono_iff hA ev).2 hb.1
    let _ : Epi ev := (NondegenerateModuleExactnessConcrete.epi_iff hA ev).2 hb.2
    let _ : IsIso ev := isIso_of_mono_of_epi ev
    let _ : Simple (rightDualObject hA (dualObject hA X)) :=
      (Simple.of_iso (asIso ev).symm : Simple ((bidualFunctor hA).obj X))
    exact simple_of_rightDual_simple hA (dualObject hA X)
  · intro hs
    let _ := hs
    exact simple_of_dual_simple hA X

end Langlands.Algebra.NonUnitalModuleAdmissibilitySimplicityProof
