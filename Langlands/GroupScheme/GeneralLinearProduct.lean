import Langlands.GroupScheme.GeneralLinear
import Langlands.GroupScheme.Products
import Langlands.GroupScheme.Multiplicative

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinearProduct

variable (n : ℕ) (I : Type u) [Finite I] (R : CommRingCat.{u})

/-- The actual product of finitely many general linear groups and a multiplicative group. -/
abbrev groupScheme : GroupScheme (Spec R) :=
  (GroupScheme.pi fun _ : I => GeneralLinear.groupScheme (Fin n) R) ⊗ (Gm (Spec R)).toGrp

/-- All test-scheme points are a family of invertible matrices and one scalar unit. -/
def pointsEquiv (T : Over (Spec R)) :
    (T ⟶ (groupScheme n I R).X) ≃*
      ((I → Matrix.GeneralLinearGroup (Fin n) Γ(T.left, ⊤)) × Γ(T.left, ⊤)ˣ) :=
  (productPointsEquiv _ _ T).trans
    (((piPointsEquiv (fun _ : I => GeneralLinear.groupScheme (Fin n) R) T).trans
      (MulEquiv.piCongrRight fun _ : I => GeneralLinear.pointsEquiv (Fin n) R T)).prodCongr
      (Gm.pointsEquiv (Spec R) T))

/-- Explicit coordinates through the categorical product projections. -/
theorem pointsEquiv_apply (T : Over (Spec R)) (x : T ⟶ (groupScheme n I R).X) :
    pointsEquiv n I R T x =
      (fun i => GeneralLinear.pointsEquiv (Fin n) R T
        (piPointsEquiv (fun _ : I => GeneralLinear.groupScheme (Fin n) R) T
          (productPointsEquiv _ _ T x).1 i),
        Gm.pointsEquiv (Spec R) T (productPointsEquiv _ _ T x).2) := rfl

/-- Precomposition pulls back every matrix entry and the scalar unit. -/
theorem pointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme n I R).X) :
    pointsEquiv n I R T' (a ≫ x) =
      (fun i => Matrix.GeneralLinearGroup.map a.left.appTop.hom
        ((pointsEquiv n I R T x).1 i),
        Units.map a.left.appTop.hom.toMonoidHom (pointsEquiv n I R T x).2) := by
  rw [pointsEquiv_apply, pointsEquiv_apply, productPointsEquiv_naturality]
  dsimp only
  rw [piPointsEquiv_naturality]
  apply Prod.ext
  · funext i
    exact GeneralLinear.pointsEquiv_naturality a _
  · exact Gm.pointsEquiv_naturality (Spec R) a _

end Langlands.GroupScheme.GeneralLinearProduct
