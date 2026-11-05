import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicDirectImageStatement
import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationBaseChange

/-! # Actual cubic evaluation and its canonical base-change compatibility -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.ProjectiveBundle

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {P : Prerequisites.{u}} {S S' : Scheme.{u}} {g d n : ℕ}

/-- Full adjoint evaluation of the actual cubic diagonal bundle. -/
def Datum.cubicEvaluationAdjoint (a : Datum P S g d n) :
    (Scheme.Modules.pullback a.abelian.X.hom).obj a.rigidificationModule ⟶
      a.cubicBundle.obj :=
  (Scheme.Modules.pullbackPushforwardAdjunction a.abelian.X.hom).counit.app
    a.cubicBundle.obj

lemma Datum.cubicEvaluationAdjoint_eq_evaluationAdjoint (a : Datum P S g d n) :
    a.cubicEvaluationAdjoint =
      evaluationAdjoint a.abelian.X.hom a.cubicBundle (𝟙 a.rigidificationModule) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction a.abelian.X.hom).homEquiv_symm_id
    a.cubicBundle.obj).symm

/-- Canonical direct-image and coefficient comparisons carry the actual
changed cubic evaluation to the pullback of the original evaluation. -/
theorem Datum.cubicEvaluationAdjoint_baseChange (a : Datum P S g d n) (b : S' ⟶ S) :
    (pullbackSquareIso b a.abelian.X.hom (a.pullback b).abelian.X.hom
        (pullback.fst a.abelian.X.hom b) pullback.condition).inv.app
        a.rigidificationModule ≫
      (Scheme.Modules.pullback (pullback.fst a.abelian.X.hom b)).map
        a.cubicEvaluationAdjoint =
    (Scheme.Modules.pullback (a.pullback b).abelian.X.hom).map
        (a.rigidificationBaseChangeMap b) ≫
      (a.pullback b).cubicEvaluationAdjoint ≫
        ((LineBundle.forget _).mapIso (a.cubicBundlePullbackIso b)).hom := by
  let e := (LineBundle.forget _).mapIso (a.cubicBundlePullbackIso b)
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction
    (a.pullback b).abelian.X.hom).counit.naturality e.inv
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have ht := baseChangeEvaluation_adjunct a.abelian.X.hom a.cubicBundle
    (𝟙 a.rigidificationModule) b (a.pullback b).abelian.X.hom
    (pullback.fst a.abelian.X.hom b) pullback.condition
  dsimp only [baseChangeEvaluation] at ht
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at ht
  rw [← a.cubicEvaluationAdjoint_eq_evaluationAdjoint] at ht
  rw [← ht, evaluationAdjoint, Adjunction.homEquiv_counit]
  dsimp only [Datum.rigidificationBaseChangeMap, Datum.cubicEvaluationAdjoint]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hn]
  erw [Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Epi canonical comparisons and epi full cubic evaluation on the actual
pulled-back residue-field data give relative cubic generation. -/
theorem Datum.cubicEvaluationGenerates_of_fibre_epi (a : Datum P S g d n)
    [a.rigidificationModule.IsQuasicoherent]
    (hbc : ∀ s : S, Epi (a.rigidificationBaseChangeMap (S.fromSpecResidueField s)))
    (hev : ∀ s : S, Epi
      ((a.pullback (S.fromSpecResidueField s)).cubicEvaluationAdjoint)) :
    EvaluationGenerates a.abelian.X.hom a.cubicBundle (𝟙 a.rigidificationModule) := by
  have : ((Scheme.Modules.pushforward a.abelian.X.hom).obj
    a.cubicBundle.obj).IsQuasicoherent := ‹a.rigidificationModule.IsQuasicoherent›
  apply evaluationGenerates_of_fibre_epi a.abelian.X.hom a.cubicBundle (𝟙 _)
  intro s
  have := hbc s
  have := hev s
  change Epi ((pullbackSquareIso (S.fromSpecResidueField s) a.abelian.X.hom
      (a.pullback (S.fromSpecResidueField s)).abelian.X.hom
      (pullback.fst a.abelian.X.hom (S.fromSpecResidueField s))
      pullback.condition).inv.app a.rigidificationModule ≫
    (Scheme.Modules.pullback (pullback.fst a.abelian.X.hom
      (S.fromSpecResidueField s))).map
      (evaluationAdjoint a.abelian.X.hom a.cubicBundle (𝟙 _)))
  rw [← a.cubicEvaluationAdjoint_eq_evaluationAdjoint,
    a.cubicEvaluationAdjoint_baseChange (S.fromSpecResidueField s)]
  infer_instance

/-- The specified direct-image theorem supplies both quasi-coherence and the
canonical comparisons in the preceding conditional generation result. -/
theorem Datum.cubicEvaluationGenerates_of_directImage
    (H : CubicDirectImageStatement.{u}) [IsLocallyNoetherian S]
    (hd : 0 < d) (a : Datum P S g d n)
    (hev : ∀ s : S, Epi
      ((a.pullback (S.fromSpecResidueField s)).cubicEvaluationAdjoint)) :
    EvaluationGenerates a.abelian.X.hom a.cubicBundle (𝟙 a.rigidificationModule) := by
  obtain ⟨hM, hbc⟩ := H P S g d n hd a
  have := hM.isLocallyFree
  have : a.rigidificationModule.IsQuasicoherent := inferInstance
  apply a.cubicEvaluationGenerates_of_fibre_epi
  · intro s
    have := hbc _ (S.fromSpecResidueField s)
    infer_instance
  · exact hev

end Langlands.AbelianScheme.PolarizedFiniteLevel
