import Langlands.Global.IntegralModelQuotientCovering
import Langlands.GroupScheme.IntegralModel.ConditionalReductiveParabolicSpreading
import Langlands.GroupScheme.IntegralModel.MaximalCompactStatement
import Langlands.GroupScheme.Reductive.GenericSpreadingProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.RelativeParabolicQuotientConstruction
import Langlands.GroupScheme.SelfNormalizingProperAmbientProof

/-! # Integral Iwasawa families reduced to supplied-model maximal compactness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.Global.IntegralIwasawaFamily

open Langlands.GroupScheme
open Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading

/-- Actual simultaneous good arithmetic models, constructed from the original
connected-reductive and parabolic hypotheses with no structural premise. -/
def goodModelData
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (hp : IsParabolicSubgroup p) :
    Σ S : Finset (FinitePlace F), ModelData ((S : Set (FinitePlace F)).integer F) F p :=
  modelDataOfSpreadingStatements genericReductivitySpreading parabolicDynamic
    F G hG P p hp

/-- Proper relative parabolic quotients are supplied by published proofs,
including the improper parabolic and arbitrary coefficient rings. -/
theorem relativeParabolicQuotient : RelativeParabolicQuotient.ExistenceStatement.{u} :=
  RelativeParabolicQuotient.existenceStatement_of_dynamic_and_ambient
    parabolicDynamic selfNormalizingProperAmbient

local instance reductionCompletionValuativeRel (F : Type u) [Field F] [NumberField F]
    (v : FinitePlace F) : ValuativeRel (FiniteCompletion F v) :=
  FiniteCompletion.valuativeRel v

/-- The single remaining structural input gives the complete original family
conclusion. This reduction does not assert that input. -/
theorem existenceStatement_of_maximalCompact
    (hmax : IntegralModel.MaximalCompactStatement.{u}) : ExistenceStatement.{u} := by
  intro F _ _ G hG P p hp
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let D := goodModelData F G hG P p hp
  refine ⟨FiniteTypeIntegralFamily.subgroup F G,
    isIntegralIwasawaFamily_of_models F G P p D.1 D.2.ambient ?_⟩
  apply ModelLocalConditions.of_quotientStatement F D.1 relativeParabolicQuotient D.2
  intro v
  have : IsNonarchimedeanLocalField (FiniteCompletion F v.1) :=
    FiniteCompletion.isNonarchimedeanLocalField v.1
  have hlocal : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v.1))).obj G) :=
    connectedReductiveFieldExtensionStatement F (FiniteCompletion F v.1) G hG
  exact (hmax (FiniteCompletion F v.1) _ hlocal
    (IntegralModelCompletions.canonicalModel F D.1 v D.2.ambient)
    (IntegralModelCompletions.canonicalModelData_specialFibre F D.1 v D.2).1).2

end Langlands.Global.IntegralIwasawaFamily
