import Langlands.GroupScheme.Dynamic.AdjointDeterminant

/-! # Functoriality target for the actual adjoint determinant -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Coefficient change and restriction of the actual action preserve the
constructed differential and algebraic determinant character. -/
def DynamicAdjointDeterminantFunctorialityStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (G P U : GroupScheme (Spec R))
    (χ : (Gm (Spec R)).toGrp ⟶ G) (iP : P ⟶ G) (iU : U ⟶ G)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)
    [IsAffineHom U.X.hom] [IsAffine P.X.left]
    (d : ℕ) (c : Lie.FiniteCoordinates U d),
    let a := Dynamic.parabolicAdjointAction hP hU
    let δ := Dynamic.adjointDeterminantCharacter hP hU c
    (∀ (A B : CommAlgCat.{u} R) (f : A ⟶ B) (p : P.affinePoints A)
      (x : Additive (lieKernel U A)),
      lieKernelMapLinear U f.hom (a.differential p x) =
        a.differential (P.affinePointMap f p) (lieKernelMapLinear U f.hom x)) ∧
    (∀ (A B : CommAlgCat.{u} R) (f : A ⟶ B) (p : P.affinePoints A),
      letI : CommGroup (lieKernel U A) := lieKernelCommGroup U
      letI : Module A (Additive (lieKernel U A)) := lieKernelModule U
      letI : CommGroup (lieKernel U B) := lieKernelCommGroup U
      letI : Module B (Additive (lieKernel U B)) := lieKernelModule U
      LinearEquiv.det (R := B) (M := Additive (lieKernel U B))
          (a.differential (P.affinePointMap f p)) =
        Units.map f.hom.toRingHom.toMonoidHom
          (LinearEquiv.det (R := A) (M := Additive (lieKernel U A))
            (a.differential p))) ∧
    (∀ (A B : CommAlgCat.{u} R) (f : A ⟶ B) (p : P.affinePoints A),
      Gm.affinePointsEquiv ((algSpec R).obj (op B)).hom
          (P.affinePointMap f p ≫ δ.toMul.hom.hom) =
        Units.map f.hom.toRingHom.toMonoidHom
          (Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom
            (p ≫ δ.toMul.hom.hom))) ∧
    (∀ (H : GroupScheme (Spec R)) [IsAffine H.X.left] (j : H ⟶ P),
      characterRestrict j δ = (a.restrict j).determinantCharacter c ∧
      ∀ (A : CommAlgCat.{u} R) (h : H.affinePoints A),
        (a.restrict j).differential h = a.differential (h ≫ j.hom.hom))

end Langlands.GroupScheme
