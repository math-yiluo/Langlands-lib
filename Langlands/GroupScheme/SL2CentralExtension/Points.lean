import Langlands.GroupScheme.SpecialLinear
import Langlands.GroupScheme.Multiplicative
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.SL2CentralExtension.Matrices
import Langlands.GroupScheme.SL2CentralExtension.Covers

/-! # Points of `SL₂` over a base scheme -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SL2CentralExtension

/-- `SL₂` over `S`: the base change of the integral special linear group scheme, exactly as in
the target statement. -/
noncomputable abbrev sl2 (S : Scheme.{u}) : GroupScheme S :=
  (GroupScheme.baseChange (Gm.toSpecZ S)).obj
    (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of (ULift.{u} ℤ)))

variable {S : Scheme.{u}}

/-- Points of `SL₂` over a test scheme `T` are determinant-one matrices over `Γ(T, ⊤)`. -/
noncomputable def slEquiv (T : Over S) : (T ⟶ (sl2 S).X) ≃* Mat.SL2 Γ(T.left, ⊤) :=
  (GroupScheme.baseChangePointsEquiv (Gm.toSpecZ S) _ T).trans
    (SpecialLinear.pointsEquiv (Fin 2) _ ((Over.map (Gm.toSpecZ S)).obj T))

/-- Restricting a point of `SL₂` applies the pullback on global sections entrywise. -/
theorem slEquiv_naturality {T V : Over S} (g : V ⟶ T) (x : T ⟶ (sl2 S).X) :
    slEquiv V (g ≫ x) = Matrix.SpecialLinearGroup.map (ring g) (slEquiv T x) := by
  simp only [slEquiv, MulEquiv.trans_apply]
  rw [GroupScheme.baseChangePointsEquiv_naturality, SpecialLinear.pointsEquiv_naturality]
  rfl

end Langlands.GroupScheme.SL2CentralExtension
