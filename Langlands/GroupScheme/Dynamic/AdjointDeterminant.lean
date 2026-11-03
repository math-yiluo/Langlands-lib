import Langlands.GroupScheme.Lie.ActionDeterminant
import Langlands.GroupScheme.Dynamic.Conjugation

/-! # Actual adjoint determinant on a represented dynamic parabolic -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section ArbitraryBase
variable {S : Scheme.{u}} {G P U : GroupScheme S} {χ : (Gm S).toGrp ⟶ G}
  {iP : P ⟶ G} {iU : U ⟶ G}
  (hP : (parabolic χ).IsRepresentedBy iP) (hU : (unipotent χ).IsRepresentedBy iU)

/-- The actual normalized conjugation action with orientation p*u*p⁻¹. -/
def parabolicAdjointAction : AutomorphicAction P U := by
  letI := hU.1
  exact AutomorphicAction.ofNormalizedConjugation iU iP
    (range_unipotent_isNormalizedBy_range_parabolic hP hU)

/-- The action morphism is the published actual parabolic conjugation morphism. -/
theorem parabolicAdjointAction_hom :
    (parabolicAdjointAction hP hU).hom = parabolicConjugation hP hU := rfl

/-- The action recovers positive-orientation conjugation after the actual inclusion. -/
theorem parabolicAdjointAction_act_comp {T : Over S}
    (p : T ⟶ P.X) (u : T ⟶ U.X) :
    (parabolicAdjointAction hP hU).act p u ≫ iU.hom.hom =
      (p ≫ iP.hom.hom) * (u ≫ iU.hom.hom) * (p ≫ iP.hom.hom)⁻¹ :=
  lift_comp_parabolicConjugation_comp hP hU p u

end ArbitraryBase

section AffineBase
variable {R : CommRingCat.{u}} {G P U : GroupScheme (Spec R)}
  {χ : (Gm (Spec R)).toGrp ⟶ G} {iP : P ⟶ G} {iU : U ⟶ G}
  (hP : (parabolic χ).IsRepresentedBy iP) (hU : (unipotent χ).IsRepresentedBy iU)
  [IsAffineHom U.X.hom] [IsAffine P.X.left] {d : ℕ}
  (c : Lie.FiniteCoordinates U d)

/-- The actual algebraic character det(Ad|Lie U) on the represented dynamic P. -/
def adjointDeterminantCharacter : rationalCharacters P :=
  (parabolicAdjointAction hP hU).determinantCharacter c

/-- Its value on every affine test is the determinant of the actual Lie action. -/
theorem adjointDeterminantCharacter_affinePoints (A : CommAlgCat.{u} R)
    (p : P.affinePoints A) :
    Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom
        (p ≫ (adjointDeterminantCharacter hP hU c).toMul.hom.hom) =
      LinearEquiv.det ((parabolicAdjointAction hP hU).differential p) :=
  (parabolicAdjointAction hP hU).determinantCharacter_affinePoints c A p

include c in
omit [IsAffine P.X.left] in
/-- Scalar extension and every other algebra map preserve the actual determinant formula. -/
theorem adjointDeterminantCharacter_differential_naturality
    {A B : CommAlgCat.{u} R} (f : A ⟶ B) (p : P.affinePoints A) :
    LinearEquiv.det ((parabolicAdjointAction hP hU).differential
      (P.affinePointMap f p)) =
      Units.map f.hom.toRingHom.toMonoidHom
        (LinearEquiv.det ((parabolicAdjointAction hP hU).differential p)) :=
  (parabolicAdjointAction hP hU).differential_det_naturality c f p

end AffineBase
end Langlands.GroupScheme.Dynamic
