import Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints
import Langlands.GroupScheme.PointCentralizer
import Langlands.GroupScheme.Torus.Maximal
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! # Regular rational points of maximal tori in the general linear group -/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

universe u

/-- Over an infinite field, each maximal torus in `GL_n` represents the
centralizer of a rational point whose matrix has separable characteristic
polynomial. -/
def GeneralLinearMaximalTorusRegularPointStatement : Prop :=
  ∀ (F : Type u) [Field F] [Infinite F] (n : ℕ),
    let G := GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (j : T.toGrp ⟶ G),
      IsMaximalTorus j →
        ∃ t : rationalPoints T.toGrp,
          let g := rationalPoints.map j t
          let matrix := GeneralLinear.rationalPointsEquiv n (CommRingCat.of F) g
          matrix.val.charpoly.Separable ∧ (G.pointCentralizer g).IsRepresentedBy j

end Langlands.GroupScheme
