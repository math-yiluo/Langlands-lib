import Langlands.GroupScheme.SchemeAction
import Langlands.GroupScheme.SchemeActionOfPointLaws
import Langlands.GroupScheme.Dynamic.FlagQuotientAction

/-! # The categorical action on an actual scheme coset quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} (G : GroupScheme S)
variable (H : SubgroupFunctor G) {Q : Over S} (q : G.X ⟶ Q)
variable (hfib : ∀ (T : Over S) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ H.carrier T)
variable [QuasiCompact q.left] [Flat q.left] [Surjective q.left]

/-- Package the descended quotient action as the standard categorical action. -/
@[instance_reducible]
def flagQuotientSchemeAction : SchemeAction G Q :=
  schemeActionOfPointLaws (flagQuotientActionHom G H q hfib)
    (fun x => flagQuotientAct_one G H q hfib x)
    (fun g h x => flagQuotientAct_mul G H q hfib g h x)

/-- The packaging retains the actual descended action morphism. -/
@[simp]
theorem flagQuotientSchemeAction_hom :
    (flagQuotientSchemeAction G H q hfib).hom = flagQuotientActionHom G H q hfib := rfl

/-- Evaluation is exactly the previously constructed all-test action. -/
@[simp]
theorem flagQuotientSchemeAction_act {T : Over S} (g : T ⟶ G.X) (x : T ⟶ Q) :
    (flagQuotientSchemeAction G H q hfib).act g x =
      flagQuotientAct G H q hfib g x := rfl

/-- The categorical action on a lifted coset is multiplication followed by q. -/
theorem flagQuotientSchemeAction_act_lift {T : Over S} (g h : T ⟶ G.X) :
    (flagQuotientSchemeAction G H q hfib).act g (h ≫ q) = (g * h) ≫ q := by
  exact flagQuotientAct_lift G H q hfib g h

end Langlands.GroupScheme.Dynamic
