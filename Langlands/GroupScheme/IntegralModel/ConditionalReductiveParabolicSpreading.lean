import Langlands.GroupScheme.IntegralModel.ArithmeticReductiveSpreading
import Langlands.GroupScheme.IntegralModel.CocharacterSpreading
import Langlands.GroupScheme.IntegralModel.DynamicParabolic
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Simultaneous spreading from generic openness and parabolic classification -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Global
open scoped NumberField

namespace Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading

open ArithmeticSpreading

/-- Construct the exact simultaneous model data from the two explicit structural
statements, choosing the generic cocharacter and its arithmetic extension. -/
def modelDataOfSpreadingStatements
    (hSpread : GenericReductivitySpreadingStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (hp : IsParabolicSubgroup p) :
    Σ S : Finset (FinitePlace F), ModelData ((S : Set (FinitePlace F)).integer F) F p := by
  let H := (hPD F G hG P p hp.isClosedSubgroup).1 hp
  let χ := H.choose
  have hχ := H.choose_spec
  let D := reductiveModelData F hSpread G hG
  let : Smooth D.model.group.X.hom := D.reductive.smooth
  let C := enlargedCocharacterData F D.places D.model χ
  let R : Type u := (C.places : Set (FinitePlace F)).integer F
  let N : IntegralModel R F G := enlargeModel F D.model C.contains
  let : IsNoetherianRing R := (adelicSIntegersNoetherian.2 F C.places).1
  let : Smooth N.group.X.hom := smooth_enlargeModel F D.model C.contains
  have hfields : ∀ (k : Type u) [Field k] [Algebra R k],
      IsConnectedReductive ((baseChange (Spec.algebraMap R k)).obj N.group) :=
    fieldReductive_enlargeModel F D.model C.contains D.fieldReductive
  have hN : IsReductive N.group :=
    isReductive_of_fieldReductive N.group inferInstance inferInstance hfields
  have : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  have hrep : (Dynamic.parabolic χ).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, hχ⟩
  have hχN : SubgroupFunctor.range (p ≫ N.genericIso.inv) =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter (Spec.algebraMap R F) C.cocharacter) := by
    rw [Dynamic.parabolic_eq_comap_of_iso _ N.genericIso, C.generic_comm]
    exact (hrep.comp_iso N.genericIso.symm).2
  exact ⟨C.places, DynamicParabolic.modelData N C.cocharacter p hp.isClosedSubgroup
    hχN hPD hN hfields⟩

/-- The exact published existence proposition follows from the explicit generic
openness and dynamic classification statements. -/
theorem existenceStatement_of_spreadingStatements
    (hSpread : GenericReductivitySpreadingStatement.{u})
    (hPD : ParabolicDynamicStatement.{u}) :
    ExistenceStatement.{u} := by
  intro F _ _ G hG P p hp
  let D := modelDataOfSpreadingStatements hSpread hPD F G hG P p hp
  exact ⟨D.1, ⟨D.2⟩⟩

end Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading
