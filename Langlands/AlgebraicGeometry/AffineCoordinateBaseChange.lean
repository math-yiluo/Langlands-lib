import Langlands.AlgebraicGeometry.ClosedFactorizationLocusStatement
import Langlands.AlgebraicGeometry.AffineClosedFactorizationLocus
import Langlands.GroupScheme.CorepresentedAffineComparison
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Affine coordinates under scalar extension -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.AffineCoordinateBaseChange

variable {R : CommRingCat.{u}}

/-- Scalar extension of an affine spectrum is the spectrum of the tensor algebra. -/
def tensorSpecIso (B A : CommAlgCat R) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj
      ((algSpec R).obj (op A)) ≅
    (algSpec (CommRingCat.of B)).obj (op (CommAlgCat.of B (B ⊗[R] A))) :=
  Over.isoMk
    (pullbackSymmetry _ _ ≪≫ pullbackSpecIso R B A) (by
      change (pullbackSymmetry
          (Spec.map (CommRingCat.ofHom (algebraMap R A)))
          (Spec.map (CommRingCat.ofHom (algebraMap R B)))).hom ≫
        (pullbackSpecIso R B A).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[R] A))) =
        pullback.snd _ _
      simp only [pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst])

/-- The affine model of a scalar extension, with its specified base algebra. -/
def baseChangeModelIso (X : Over (Spec R)) [IsAffine X.left] (B : CommAlgCat R) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj X ≅
    (algSpec (CommRingCat.of B)).obj
      (op (CommAlgCat.of B (B ⊗[R] ((algΓ R).obj X).unop))) :=
  (Over.pullback _).mapIso (AffineClosedFactorizationLocus.coordinateIso R X) ≪≫
    tensorSpecIso B _

/-- The coordinate algebra of the scalar extension is the tensor algebra. -/
def baseChangeSectionsIso (X : Over (Spec R)) [IsAffine X.left] (B : CommAlgCat R) :
    ((algΓ (CommRingCat.of B)).obj
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj X)).unop ≅
        CommAlgCat.of B (B ⊗[R] ((algΓ R).obj X).unop) :=
  ((algΓ (CommRingCat.of B)).mapIso (baseChangeModelIso X B)).unop.symm ≪≫
    Langlands.GroupScheme.Corepresented.affineSectionsIso _

/-- Projectivity of the tensor module is projectivity of the changed coordinates. -/
theorem projective (X : Over (Spec R)) [IsAffine X.left] (B : CommAlgCat R)
    [Module.Projective B (B ⊗[R] ((algΓ R).obj X).unop)] :
    Module.Projective B (((algΓ (CommRingCat.of B)).obj
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj X)).unop) :=
  Module.Projective.of_equiv'
    (CommAlgCat.algEquivOfIso (baseChangeSectionsIso X B).symm).toLinearEquiv

end Langlands.AlgebraicGeometry.AffineCoordinateBaseChange
