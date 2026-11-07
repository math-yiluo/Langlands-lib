import Langlands.GroupScheme.IntegralModel.ArithmeticReductiveSpreading
import Langlands.GroupScheme.IntegralModel.CocharacterSpreading
import Langlands.GroupScheme.IntegralModel.DynamicParabolic
import Langlands.GroupScheme.Absolute.DynamicParabolicRecognition
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Simultaneous spreading from a generic cocharacter -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Global
open scoped NumberField

namespace Langlands.GroupScheme.IntegralModel

namespace DynamicParabolic

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G P : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)

local instance : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom

variable (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ M.group)
  (p : P ⟶ G) (hp : IsClosedSubgroup p)
  (hχ : SubgroupFunctor.range (p ≫ M.genericIso.inv) =
    Dynamic.parabolic (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ))
  [IsNoetherianRing R] [Smooth M.group.X.hom]

/-- Every field fibre of the actual dynamic inclusion is geometrically parabolic
from connected reductivity, without a parabolic classification premise. -/
theorem fieldParabolic_of_connectedReductive
    (k : Type u) [Field k] [Algebra R k]
    (hG : IsConnectedReductive ((baseChange (Spec.algebraMap R k)).obj M.group)) :
    IsParabolicSubgroup ((baseChange (Spec.algebraMap R k)).map
      (inclusion M χ p hp hχ).hom) :=
  isParabolicSubgroup_of_range_eq_dynamicParabolic hG _
    ((Dynamic.Affine.isClosedSubgroup_parabolicHom χ).baseChange (Spec.algebraMap R k))
    (Dynamic.baseChangeCocharacter (Spec.algebraMap R k) χ)
    (Dynamic.Affine.isRepresentedBy_parabolicHom_baseChange χ (Spec.algebraMap R k)).2

/-- The exact simultaneous model data from a descended cocharacter and good
ambient fibres, with no classification statement as an input. -/
def modelDataOfCocharacter (hM : IsReductive M.group)
    (hfields : ∀ (k : Type u) [Field k] [Algebra R k],
      IsConnectedReductive ((baseChange (Spec.algebraMap R k)).obj M.group)) :
    ReductiveParabolicSpreading.ModelData R K p where
  ambient := M
  parabolic := model M χ p hp hχ
  inclusion := inclusion M χ p hp hχ
  closedImmersion := closedImmersion_inclusion M χ p hp hχ
  reductive := hM
  parabolicSmooth := smooth_model M χ p hp hχ
  fieldReductive := hfields
  fieldParabolic k := fieldParabolic_of_connectedReductive M χ p hp hχ k (hfields k)
  fieldConnected k := fieldConnected M χ p hp hχ k (hfields k)

end DynamicParabolic

namespace ReductiveParabolicSpreading

open ArithmeticSpreading

/-- Construct a simultaneous model over a finite S-integer ring from generic
reductivity spreading and an actual generic cocharacter presentation. -/
def modelDataOfGenericCocharacter
    (hSpread : GenericReductivitySpreadingStatement.{u})
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (hp : IsClosedSubgroup p)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hχ : SubgroupFunctor.range p = Dynamic.parabolic χ) :
    Σ S : Finset (FinitePlace F), ModelData ((S : Set (FinitePlace F)).integer F) F p := by
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
  have : IsClosedImmersion p.hom.hom.left := hp
  have hrep : (Dynamic.parabolic χ).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, hχ⟩
  have hχN : SubgroupFunctor.range (p ≫ N.genericIso.inv) =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter (Spec.algebraMap R F) C.cocharacter) := by
    rw [Dynamic.parabolic_eq_comap_of_iso _ N.genericIso, C.generic_comm]
    exact (hrep.comp_iso N.genericIso.symm).2
  exact ⟨C.places, DynamicParabolic.modelDataOfCocharacter N C.cocharacter p hp hχN
    hN hfields⟩

end ReductiveParabolicSpreading
end Langlands.GroupScheme.IntegralModel
