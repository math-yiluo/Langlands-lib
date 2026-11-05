import Langlands.GroupScheme.SplitExistence.NegGroup
import Langlands.GroupScheme.Lie.GeneralLinearAdjoint
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Torus.Weights
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal

/-! # Matrix coordinates on the Lie algebra of the Chevalley group

The closed embedding `i : G ⟶ GL_n` identifies the Library Lie algebra `lieKernel G A` with a
space of `n × n` matrices over `A`. In these coordinates the adjoint action of a point is
conjugation by its matrix, and change of coefficients acts entrywise. Points of the torus act
through the diagonal matrices `diag(χ(wt c))`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

/-- The tangent map of a homomorphism commutes with the adjoint actions. -/
theorem targetMapLinear_adjoint {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] (f : G ⟶ H) (A : Type u) [CommRing A]
    [Algebra R A] (g : Lie.AffinePoints G A) (x : Additive (lieKernel G A)) :
    Lie.targetMapLinear f A (adjoint G A g x) =
      adjoint H A (g ≫ f.hom.hom) (Lie.targetMapLinear f A x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change (Lie.constant G g * x.toMul.val * (Lie.constant G g)⁻¹) ≫ f.hom.hom =
    Lie.constant H (g ≫ f.hom.hom) * (x.toMul.val ≫ f.hom.hom) *
      (Lie.constant H (g ≫ f.hom.hom))⁻¹
  have hc : Lie.constant G g ≫ f.hom.hom = Lie.constant H (g ≫ f.hom.hom) := by
    change (_ ≫ g) ≫ f.hom.hom = _ ≫ (g ≫ f.hom.hom)
    rw [Category.assoc]
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hc]

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  {D : ChevalleyData P b} {k : Type u} [Field k]

instance isAffineHom_GLk : IsAffineHom (D.GLk k).X.hom := GeneralLinear.isAffineHom_groupScheme _ _

namespace ChevGroup

variable (G : D.ChevGroup k) [IsAffineHom G.H.X.hom]

open GeneralLinear.DualNumber

/-- The matrix coordinates of the Lie algebra of `G` over a `k`-algebra `A`. -/
def lieMat (A : Type u) [CommRing A] [Algebra k A] :
    Additive (lieKernel G.H A) →ₗ[A] Matrix (Fin D.n) (Fin D.n) A :=
  (pointKernelLinearEquiv (n := Fin D.n) (R := CommRingCat.of k) (A := A)).symm.toLinearMap ∘ₗ
    Lie.targetMapLinear G.i A

theorem lieMat_apply (A : Type u) [CommRing A] [Algebra k A] (x : Additive (lieKernel G.H A)) :
    G.lieMat A x = coefficients (GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k)
      (CommAlgCat.of k (DualNumber A)) (x.toMul.val ≫ G.i.hom.hom)) :=
  rfl

theorem lieMat_injective (A : Type u) [CommRing A] [Algebra k A] :
    Function.Injective (G.lieMat A) := by
  have := G.mono_i
  exact (pointKernelLinearEquiv (n := Fin D.n) (R := CommRingCat.of k) (A := A)).symm.injective.comp
    (Lie.targetMapLinear_injective G.i A)

/-- In matrix coordinates the adjoint action is conjugation. -/
theorem lieMat_adjoint (A : Type u) [CommRing A] [Algebra k A] (g : Lie.AffinePoints G.H A)
    (x : Additive (lieKernel G.H A)) :
    G.lieMat A (adjoint G.H A g x) =
      (GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) (CommAlgCat.of k A)
          (g ≫ G.i.hom.hom) : Matrix (Fin D.n) (Fin D.n) A) * G.lieMat A x *
        (((GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) (CommAlgCat.of k A)
          (g ≫ G.i.hom.hom))⁻¹ : GL (Fin D.n) A) : Matrix (Fin D.n) (Fin D.n) A) := by
  change (pointKernelLinearEquiv (n := Fin D.n) (R := CommRingCat.of k) (A := A)).symm
    (Lie.targetMapLinear G.i A (adjoint G.H A g x)) = _
  rw [targetMapLinear_adjoint]
  conv_lhs => rw [← (pointKernelLinearEquiv (n := Fin D.n) (R := CommRingCat.of k)
    (A := A)).apply_symm_apply (Lie.targetMapLinear G.i A x)]
  rw [adjoint_pointKernelLinearEquiv, LinearEquiv.symm_apply_apply]
  rfl

/-- Change of coefficients acts entrywise on matrix coordinates. -/
theorem lieMat_map {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (x : Additive (lieKernel G.H A)) :
    G.lieMat B (lieKernelMapLinear G.H f x) = (G.lieMat A x).map f := by
  change (pointKernelLinearEquiv (n := Fin D.n) (R := CommRingCat.of k) (A := B)).symm
    (Lie.targetMapLinear G.i B (lieKernelMapLinear G.H f x)) = _
  rw [lieKernelTargetLinear_map]
  conv_lhs => rw [← (pointKernelLinearEquiv (n := Fin D.n) (R := CommRingCat.of k)
    (A := A)).apply_symm_apply (Lie.targetMapLinear G.i A x)]
  rw [pointKernelLinearEquiv_naturality, LinearEquiv.symm_apply_apply]
  rfl

end ChevGroup

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
