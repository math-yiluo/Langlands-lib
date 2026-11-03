import Langlands.GroupScheme.Dynamic.AdjointDeterminant
import Langlands.GroupScheme.Dynamic.CentralizerAdjointAction
import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.GroupScheme.Reductive.Basic

/-! # Existence target for the actual adjoint determinant on P and M -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Connected reductivity supplies coordinates, the actual differential
representation, and its determinant character on P and M. -/
def DynamicAdjointDeterminantExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (iP : P ⟶ G) (iM : M ⟶ G) (iU : U ⟶ G)
      (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
      (hM : (Dynamic.centralizer χ).IsRepresentedBy iM)
      (hU : (Dynamic.unipotent χ).IsRepresentedBy iU),
      ∃ (hPa : IsAffineHom P.X.hom) (hMa : IsAffineHom M.X.hom)
        (hUa : IsAffineHom U.X.hom),
        letI := hPa
        letI := hMa
        letI := hUa
        letI : IsAffine P.X.left := isAffine_of_isAffineHom P.X.hom
        letI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
        ∃ (d : ℕ) (c : Lie.FiniteCoordinates U d)
          (ρ : MatrixRepresentation P (Fin d))
          (δP : rationalCharacters P) (δM : rationalCharacters M),
          ρ = (Dynamic.parabolicAdjointAction hP hU).finiteRepresentation c ∧
          δP = Dynamic.adjointDeterminantCharacter hP hU c ∧
          δM = characterRestrict (Dynamic.centralizerToParabolic hP hM) δP ∧
          δM = (Dynamic.centralizerAdjointAction hM hU).determinantCharacter c ∧
          (∀ (A : CommAlgCat.{u} (CommRingCat.of k)) (p : P.affinePoints A)
            (x : Additive (lieKernel U A)),
            ρ.affineAction A p (c.equiv A x) =
              c.equiv A ((Dynamic.parabolicAdjointAction hP hU).differential p x)) ∧
          (∀ (A : CommAlgCat.{u} (CommRingCat.of k)) (p : P.affinePoints A),
            letI : CommGroup (lieKernel U A) := lieKernelCommGroup U
            letI : Module A (Additive (lieKernel U A)) := lieKernelModule U
            Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom
              (p ≫ δP.toMul.hom.hom) =
              LinearEquiv.det (R := A) (M := Additive (lieKernel U A))
                ((Dynamic.parabolicAdjointAction hP hU).differential p)) ∧
          (∀ (A : CommAlgCat.{u} (CommRingCat.of k)) (m : M.affinePoints A),
            letI : CommGroup (lieKernel U A) := lieKernelCommGroup U
            letI : Module A (Additive (lieKernel U A)) := lieKernelModule U
            Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom
              (m ≫ δM.toMul.hom.hom) =
              LinearEquiv.det (R := A) (M := Additive (lieKernel U A))
                ((Dynamic.centralizerAdjointAction hM hU).differential m))

end Langlands.GroupScheme
