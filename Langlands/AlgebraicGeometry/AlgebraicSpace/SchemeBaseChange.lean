import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Scheme representation under restriction to a base scheme -/

universe u

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Functor

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S T : Scheme.{u}} (g : T ⟶ S) (G : Over S)

/-- Restriction of a scheme's functor of points is represented by its
actual base change. -/
def schemeYonedaBaseChangeIso :
    (schemeYoneda T).obj ((Over.pullback g).obj G) ≅
      (Over.map g).op ⋙ (schemeYoneda S).obj G :=
  NatIso.ofComponents (fun Z =>
    (Equiv.ulift.trans
      (((Over.mapPullbackAdj g).homEquiv Z.unop G).symm.trans
        Equiv.ulift.symm)).toIso) (by
    intro Z W h
    ext a
    exact congrArg ULift.up
      ((Over.mapPullbackAdj g).homEquiv_naturality_left_symm h.unop a.down))

/-- A full natural scheme representation restricts by the same base change. -/
def representedBaseChangeIso {F : Presheaf S}
    (e : (schemeYoneda S).obj G ≅ F) :
    (schemeYoneda T).obj ((Over.pullback g).obj G) ≅
      (Over.map g).op ⋙ F :=
  schemeYonedaBaseChangeIso g G ≪≫ isoWhiskerLeft (Over.map g).op e

end Langlands.AlgebraicGeometry.AlgebraicSpace
