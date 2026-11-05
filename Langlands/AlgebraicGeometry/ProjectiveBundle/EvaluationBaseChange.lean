import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationFibres
import Langlands.AlgebraicGeometry.Modules.GeometricModuleCoalgebra

/-! # Adjoint evaluation and the canonical direct-image base-change map -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Modules.GeometricModuleCoalgebra

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

section Square

variable {X S X' S' : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X)
    {M : S.Modules} (ev : M ⟶ (Scheme.Modules.pushforward p).obj L.obj)
    (g : S' ⟶ S) (p' : X' ⟶ S') (q : X' ⟶ X) (w : q ≫ p = p' ≫ g)

/-- Evaluation after change of base uses the specified canonical direct-image
comparison, with no invertibility assumption on that comparison. -/
def baseChangeEvaluation :
    (Scheme.Modules.pullback g).obj M ⟶
      (Scheme.Modules.pushforward p').obj ((LineBundle.pullback q).obj L).obj :=
  (Scheme.Modules.pullback g).map ev ≫ pushforwardBaseChange g p p' q w L.obj

/-- The adjoint of the canonical changed evaluation is the pullback of the
original adjoint, with the source identified by the actual square comparison. -/
theorem baseChangeEvaluation_adjunct :
    evaluationAdjoint p' ((LineBundle.pullback q).obj L)
        (baseChangeEvaluation p L ev g p' q w) =
      (pullbackSquareIso g p p' q w).inv.app M ≫
        (Scheme.Modules.pullback q).map (evaluationAdjoint p L ev) := by
  have hn := (pullbackSquareIso g p p' q w).inv.naturality ev
  dsimp only [Functor.comp_map] at hn
  dsimp only [evaluationAdjoint, baseChangeEvaluation]
  rw [pushforwardBaseChange_eq_unit_comp_counit,
    Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_symm_unit]
  simp only [Category.id_comp]
  rw [reassoc_of% hn, ← Functor.map_comp, Adjunction.homEquiv_counit]

end Square

variable {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X)

/-- For the full direct image, the original fibre adjoint factors through the
canonical fibre base-change map and the full evaluation on the fibre. -/
lemma fibreEvaluationAdjoint_id_eq (s : S) :
    fibreEvaluationAdjoint p L (𝟙 ((Scheme.Modules.pushforward p).obj L.obj)) s =
      (Scheme.Modules.pullback (p.fiberToSpecResidueField s)).map
          (pushforwardBaseChange (S.fromSpecResidueField s) p
            (p.fiberToSpecResidueField s) (p.fiberι s) (p.fiber_fac s) L.obj) ≫
        evaluationAdjoint (p.fiberToSpecResidueField s)
          ((LineBundle.pullback (p.fiberι s)).obj L) (𝟙 _) := by
  have h := baseChangeEvaluation_adjunct p L
    (𝟙 ((Scheme.Modules.pushforward p).obj L.obj))
    (S.fromSpecResidueField s) (p.fiberToSpecResidueField s) (p.fiberι s) (p.fiber_fac s)
  dsimp only [baseChangeEvaluation] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  rw [evaluationAdjoint, Adjunction.homEquiv_counit] at h
  conv_rhs =>
    rw [evaluationAdjoint, Adjunction.homEquiv_counit]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact h.symm

/-- Epimorphic canonical base change and full fibre evaluation imply generation
by sections of the original direct image. -/
theorem evaluationGenerates_of_fibre_baseChange_epi
    [((Scheme.Modules.pushforward p).obj L.obj).IsQuasicoherent]
    (hbc : ∀ s : S, Epi (pushforwardBaseChange (S.fromSpecResidueField s) p
      (p.fiberToSpecResidueField s) (p.fiberι s) (p.fiber_fac s) L.obj))
    (hev : ∀ s : S, Epi (evaluationAdjoint (p.fiberToSpecResidueField s)
      ((LineBundle.pullback (p.fiberι s)).obj L) (𝟙 _))) :
    EvaluationGenerates p L (𝟙 _) := by
  apply evaluationGenerates_of_fibre_epi p L (𝟙 _)
  intro s
  have := hbc s
  have := hev s
  rw [fibreEvaluationAdjoint_id_eq]
  infer_instance

end Langlands.AlgebraicGeometry.ProjectiveBundle
