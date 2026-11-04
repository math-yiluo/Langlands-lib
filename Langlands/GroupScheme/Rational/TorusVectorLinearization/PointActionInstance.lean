import Langlands.GroupScheme.Rational.TorusLinearization.PointAction
import Langlands.GroupScheme.Rational.TorusVectorLinearization.SplitPoints
import Langlands.GroupScheme.Rational.TorusVectorLinearization.PolynomialTransition

/-! # A torus action on a vector group as an abstract point action -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

open TorusLinearization

set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {T V : GroupScheme (Spec (CommRingCat.of k))} {I : Type u} [Finite I] {n : ℕ}
    (s : (GroupScheme.baseChange (algebraBaseMap k K)).obj T ≅
      splitTorus (Spec (CommRingCat.of K)) I)
    (a : AutomorphicAction T V)
    {e : ∀ W : Over (Spec (CommRingCat.of k)),
      (W ⟶ V.X) ≃* Multiplicative (Fin n → Γ(W.left, ⊤))}
    (he : IsNaturalVectorCoordinates e)

/-- The action of a torus `T` on a vector group, in natural coordinates `e`, as an
abstract action on coordinate vectors described on points, with the points of `T`
over algebras over the splitting field parametrized through the splitting `s`. -/
def torusPointAction : PointAction k K I n where
  Pt B _ _ := Lie.AffinePoints T B
  map g t := Lie.affineMap T g t
  map_id t := Lie.affineMap_id T t
  map_comp g h t := Lie.affineMap_comp T g h t
  act t x := coordinateAction a e t x
  act_add t x y := map_add _ x y
  act_map g t x := coordinateAction_naturality a he g t x
  σ τ := splitPoint s τ
  σ_surj t := splitPoint_surjective s t
  map_σ f τ := splitPoint_naturality s f τ
  act_σ_one x := by
    simp only [splitPoint_one, coordinateAction_one]
  act_σ_mul τ τ' x := by
    simp only [splitPoint_mul, coordinateAction_mul]

theorem torusPointAction_act {B : Type u} [CommRing B] [Algebra k B]
    (t : Lie.AffinePoints T B) (x : Fin n → B) :
    (torusPointAction s a he).act (B := B) t x = coordinateAction a e t x := rfl

end Langlands.GroupScheme.RelativeRoot
