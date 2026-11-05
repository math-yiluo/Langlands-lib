import Langlands.GroupScheme.Reductive.GenericSpreadingStatement
import Langlands.GroupScheme.IntegralModel.PrincipalOpenFibers
import Langlands.GroupScheme.IntegralModel.ArithmeticHomSpreading
import Langlands.Global.AdelicSIntegersNoetherianProof

/-! # Good arithmetic ambient models from generic reductivity openness -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Global
open scoped NumberField

namespace Langlands.GroupScheme.IntegralModel.ArithmeticSpreading

variable (F : Type u) [Field F] [NumberField F]

/-- An actual arithmetic reductive model with connected reductivity at every
field-valued point of its actual integral base. -/
structure ReductiveModelData (G : GroupScheme (Spec (CommRingCat.of F))) where
  places : Finset (FinitePlace F)
  model : IntegralModel ((places : Set (FinitePlace F)).integer F) F G
  reductive : IsReductive model.group
  fieldReductive : ∀ (k : Type u) [Field k]
    [Algebra ((places : Set (FinitePlace F)).integer F) k],
    IsConnectedReductive ((baseChange
      (Spec.algebraMap ((places : Set (FinitePlace F)).integer F) k)).obj model.group)

/-- Construct a good actual arithmetic ambient model, conditional only on the
precise generic reductivity openness statement. -/
def reductiveModelData (hSpread : GenericReductivitySpreadingStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G) :
    ReductiveModelData F G := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let D := smoothIntegralModelData F G
  let S := D.1
  let R : Type u := (S : Set (FinitePlace F)).integer F
  let M : IntegralModel R F G := D.2.1
  let : Smooth M.group.X.hom := D.2.2
  let : IsNoetherianRing R := (adelicSIntegersNoetherian.2 F S).1
  have hgeneric : IsConnectedReductive
      ((baseChange (Spec.algebraMap R F)).obj M.group) :=
    hG.of_iso M.genericIso
  have h := hSpread R F M.group inferInstance inferInstance hgeneric
  let r := h.choose
  have hr : r ≠ 0 := h.choose_spec.1
  let T := numberFieldSIntegersUnitStage F S r hr
  let N := enlargeModel F M T.1.property
  let : Smooth N.group.X.hom := smooth_enlargeModel F M T.1.property
  have hfields : ∀ (k : Type u) [Field k]
      [Algebra ((T.1.val : Set (FinitePlace F)).integer F) k],
      IsConnectedReductive ((baseChange
        (Spec.algebraMap ((T.1.val : Set (FinitePlace F)).integer F) k)).obj N.group) :=
    fieldReductive_baseChange_of_isUnit
      (numberFieldSIntegersMap F T.1.property) M.group r T.2 h.choose_spec.2
  exact
    { places := T.1.val
      model := N
      reductive := isReductive_of_fieldReductive N.group inferInstance inferInstance hfields
      fieldReductive := hfields }

/-- Canonical finite enlargement preserves every actual connected reductive
field fibre of a supplied arithmetic model. -/
theorem fieldReductive_enlargeModel {S T : Finset (FinitePlace F)}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    (M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G) (hST : S ⊆ T)
    (h : ∀ (k : Type u) [Field k] [Algebra ((S : Set (FinitePlace F)).integer F) k],
      IsConnectedReductive ((baseChange
        (Spec.algebraMap ((S : Set (FinitePlace F)).integer F) k)).obj M.group)) :
    ∀ (k : Type u) [Field k] [Algebra ((T : Set (FinitePlace F)).integer F) k],
      IsConnectedReductive ((baseChange
        (Spec.algebraMap ((T : Set (FinitePlace F)).integer F) k)).obj
          (enlargeModel F M hST).group) := by
  exact fieldReductive_baseChange_of_isUnit (numberFieldSIntegersMap F hST) M.group 1
    (by simp) (fun k _ _ _ => h k)

end Langlands.GroupScheme.IntegralModel.ArithmeticSpreading
