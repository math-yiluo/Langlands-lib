import Langlands.Geometry.Building.KPZeroSubgroups

/-!
# Independence of `H(K)^0` from its defining data (KP Lemma 2.6.24)

Statement, not proof: the subgroup `H(K)^0 = H(K)^♮ · T(K)^0` of KP Definition 2.6.23(1)
does not depend on the data `UnramifiedZeroDatum F H` used to define it.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- KP Lemma 2.6.24, independence part, for Definition 2.6.23(1) over the maximal unramified
extension `K` of a nonarchimedean local field `F`: any two data for `H(K)^0` (a maximally
split maximal torus with a finite Galois splitting field `L ⊆ F^sep`, and a simply connected
cover of the derived subgroup) define the same subgroup `H(K)^♮ · T(K)^0` of `H(K)`. -/
def UnramifiedZeroPointsIndependenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
    (E E' : UnramifiedZeroDatum F H), E.zeroPoints = E'.zeroPoints

end Langlands.Geometry.Building
