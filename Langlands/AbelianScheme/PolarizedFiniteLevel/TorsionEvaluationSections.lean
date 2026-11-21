import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocus
import Langlands.AlgebraicGeometry.Modules.SectionPullbackBridge
import Langlands.AlgebraicGeometry.Modules.PullbackAffineSections
import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationAdjoint

/-! # Torsion evaluations on global sections -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule

universe u

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n : ℕ}

export Langlands.Scheme.Modules (pullback_map_app_sectionPullbackLE)

/-- The inverse identity comparison sends a section to its pullback along the identity. -/
lemma pullbackId_inv_app_eq_sectionPullbackLE {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackId X).inv.app M).app U m =
      sectionPullbackLE (𝟙 X) M (le_refl U) m := by
  rw [sectionPullbackLE_self]
  conv_lhs => rw [← sectionPullback_id M U m]
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, ← NatTrans.comp_app,
    Iso.hom_inv_id, NatTrans.id_app, Scheme.Modules.Hom.id_app]
  rfl

/-- On global sections, the torsion evaluation of a datum is the pullback of the
corresponding cubic-bundle section along the torsion point. -/
theorem Datum.torsionEvaluation_app_top (a : Datum P S g d n) (r : Fin (2 * g) → ZMod n)
    (σ : Γ(a.rigidificationModule, ⊤)) :
    (a.torsionEvaluation r).app ⊤ σ =
      pullbackSection (a.torsionPoint r) a.cubicBundle.obj σ := by
  rw [pullbackSection_eq_sectionPullback, ← sectionPullbackLE_self]
  have e1 := pullbackId_inv_app_eq_sectionPullbackLE a.rigidificationModule ⊤ σ
  have e2 := pullbackCongr_hom_sectionPullbackLE (a.torsionPoint_hom r).symm
    a.rigidificationModule (le_refl ⊤) le_top σ
  have e3 := pullbackComp_inv_sectionPullbackLE (a.torsionPoint r) a.abelian.X.hom
    a.rigidificationModule (W := ⊤) (le_refl (a.abelian.X.hom ⁻¹ᵁ ⊤)) le_top le_top σ
  have e4 := pullback_map_app_sectionPullbackLE (a.torsionPoint r) a.cubicEvaluationAdjoint
    (U := ⊤) (V := a.abelian.X.hom ⁻¹ᵁ ⊤) le_top
    (sectionPullbackLE a.abelian.X.hom a.rigidificationModule
      (le_refl (a.abelian.X.hom ⁻¹ᵁ ⊤)) σ)
  have e5 : a.cubicEvaluationAdjoint.app (a.abelian.X.hom ⁻¹ᵁ ⊤)
      (sectionPullbackLE a.abelian.X.hom a.rigidificationModule
        (le_refl (a.abelian.X.hom ⁻¹ᵁ ⊤)) σ) = σ := by
    rw [sectionPullbackLE_self, Datum.cubicEvaluationAdjoint_eq_evaluationAdjoint,
      Langlands.AlgebraicGeometry.ProjectiveBundle.evaluationAdjoint_sectionPullback]
    rfl
  rw [e5] at e4
  calc (a.torsionEvaluation r).app ⊤ σ =
      ((Scheme.Modules.pullback (a.torsionPoint r)).map a.cubicEvaluationAdjoint).app ⊤
        (((Scheme.Modules.pullbackComp (a.torsionPoint r) a.abelian.X.hom).inv.app
          a.rigidificationModule).app ⊤
          (((Scheme.Modules.pullbackCongr (a.torsionPoint_hom r).symm).hom.app
            a.rigidificationModule).app ⊤
            (((Scheme.Modules.pullbackId S).inv.app a.rigidificationModule).app ⊤ σ))) := rfl
    _ = _ := by rw [e1, e2, e3, e4]

end Langlands.AbelianScheme.PolarizedFiniteLevel
