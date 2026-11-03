import Langlands.GroupScheme.Dynamic.AdjointDeterminant

/-! # Exact all-test formula target for the actual adjoint determinant -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The constructed character is the determinant of the actual conjugation
differential, on every affine test and every scheme test. -/
def DynamicAdjointDeterminantFormulaStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (G P U : GroupScheme (Spec R))
    (χ : (Gm (Spec R)).toGrp ⟶ G) (iP : P ⟶ G) (iU : U ⟶ G)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)
    [IsAffineHom U.X.hom] [IsAffine P.X.left]
    (d : ℕ) (c : Lie.FiniteCoordinates U d),
    let a := Dynamic.parabolicAdjointAction hP hU
    let ρ := a.finiteRepresentation c
    let δ := Dynamic.adjointDeterminantCharacter hP hU c
    (∀ (T : Over (Spec R)) (p : T ⟶ P.X) (u : T ⟶ U.X),
      a.act p u ≫ iU.hom.hom =
        (p ≫ iP.hom.hom) * (u ≫ iU.hom.hom) * (p ≫ iP.hom.hom)⁻¹) ∧
    (∀ (A : CommAlgCat.{u} R) (p : P.affinePoints A)
      (x : Additive (lieKernel U A)),
      ρ.affineAction A p (c.equiv A x) = c.equiv A (a.differential p x)) ∧
    (∀ (A : CommAlgCat.{u} R) (p : P.affinePoints A),
      letI : CommGroup (lieKernel U A) := lieKernelCommGroup U
      letI : Module A (Additive (lieKernel U A)) := lieKernelModule U
      Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom (p ≫ δ.toMul.hom.hom) =
        LinearEquiv.det (R := A) (M := Additive (lieKernel U A)) (a.differential p)) ∧
    (∀ (T : Over (Spec R)) (p : T ⟶ P.X),
      characterEval δ T p = Matrix.GeneralLinearGroup.det (ρ.pointMatrix T p))

end Langlands.GroupScheme
