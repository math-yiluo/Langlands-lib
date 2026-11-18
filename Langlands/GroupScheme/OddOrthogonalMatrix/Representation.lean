import Langlands.GroupScheme.OddOrthogonalMatrix.Smooth
import Langlands.GroupScheme.Lie.RepresentationDifferential

/-! # The faithful standard representation and linear Lie coordinates -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

open Quaternionic.FirstKindInvolution Quaternionic.ScalarMatrixCoordinates
open GeneralLinear.DualNumber

variable {l : Type} [Fintype l] [DecidableEq l] (K : Type u) [Field K]

local notation "𝕌" => CentralSimpleUnits.groupScheme K (Matrix (Index l) (Index l) K)
local notation "𝔻" => CommAlgCat.of (CommRingCat.of K) (DualNumber K)

/-- Invertible matrix coordinates of an actual point over any test scheme. -/
def pointMatrix (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (groupScheme l K).X) →* Matrix.GeneralLinearGroup (Index l) Γ(T.left, ⊤) :=
  (Units.mapEquiv (matrixEquiv (n := Index l) K
    ((algΓ (CommRingCat.of K)).obj T).unop).toMulEquiv).toMonoidHom.comp
    ((FiniteAlgebraUnits.pointsEquiv
      (Module.finBasis K (Matrix (Index l) (Index l) K)) T).toMonoidHom.comp
        ((pointsMap ((scalar K).normOneIsometryAmbientι (form l K))).app (op T)).hom)

/-- The all-test matrix agrees with the earlier ambient matrix coordinates. -/
theorem pointMatrix_val (T : Over (Spec (CommRingCat.of K)))
    (z : T ⟶ (groupScheme l K).X) :
    (pointMatrix K T z : Matrix (Index l) (Index l) Γ(T.left, ⊤)) =
      ambientMatrix K T (z ≫ ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom) := rfl

/-- Pullback of any test scheme applies its section homomorphism entrywise. -/
theorem pointMatrix_naturality {T T' : Over (Spec (CommRingCat.of K))}
    (b : T' ⟶ T) (z : T ⟶ (groupScheme l K).X) :
    pointMatrix K T' (b ≫ z) =
      Matrix.GeneralLinearGroup.map b.left.appTop.hom (pointMatrix K T z) := by
  apply Units.ext
  change ambientMatrix K T' ((b ≫ z) ≫
    ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom) =
      (ambientMatrix K T (z ≫ ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom)).map
        b.left.appTop.hom
  rw [Category.assoc, ambientMatrix_naturality]
  rfl

/-- The corresponding actual general-linear point on each test scheme. -/
def inclusionPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (groupScheme l K).X) →*
      (T ⟶ (GeneralLinear.groupScheme (Index l) (CommRingCat.of K)).X) :=
  (GeneralLinear.pointsEquiv (Index l) (CommRingCat.of K) T).symm.toMonoidHom.comp
    (pointMatrix K T)

/-- Naturality of the matrix inclusion on all tests. -/
theorem inclusionPoints_naturality {T T' : Over (Spec (CommRingCat.of K))}
    (b : T' ⟶ T) (z : T ⟶ (groupScheme l K).X) :
    inclusionPoints K T' (b ≫ z) = b ≫ inclusionPoints K T z := by
  apply (GeneralLinear.pointsEquiv (Index l) (CommRingCat.of K) T').injective
  simp only [inclusionPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, GeneralLinear.pointsEquiv_naturality, pointMatrix_naturality]

/-- The actual faithful standard representation of the odd norm-one group. -/
def inclusion : MatrixRepresentation (groupScheme l K) (Index l) :=
  homOfPoints (inclusionPoints K) (inclusionPoints_naturality K)

/-- The inclusion has the prescribed matrix on every actual test scheme. -/
theorem pointsEquiv_inclusion (T : Over (Spec (CommRingCat.of K)))
    (z : T ⟶ (groupScheme l K).X) :
    GeneralLinear.pointsEquiv (Index l) (CommRingCat.of K) T
      (z ≫ (inclusion K).hom.hom) = pointMatrix K T z := by
  rw [inclusion, comp_homOfPoints]
  exact (GeneralLinear.pointsEquiv (Index l) (CommRingCat.of K) T).apply_symm_apply _

instance mono_inclusion : Mono (inclusion (l := l) K).hom.hom := by
  constructor
  intro T x y h
  apply (cancel_mono ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom).mp
  apply ambientMatrix_injective K T
  have hm := congrArg (GeneralLinear.pointsEquiv (Index l) (CommRingCat.of K) T) h
  rw [pointsEquiv_inclusion, pointsEquiv_inclusion] at hm
  exact congrArg Units.val hm

/-- On affine coefficient algebras the representation recovers the exact
previously constructed coefficient matrix. -/
theorem affinePointsEquiv_inclusion (A : CommAlgCat.{u} (CommRingCat.of K))
    (z : (algSpec (CommRingCat.of K)).obj (op A) ⟶ (groupScheme l K).X) :
    GeneralLinear.affinePointsEquiv (Index l) (CommRingCat.of K) A
      (z ≫ (inclusion K).hom.hom) = affineMatrix K A z := by
  have h := Corepresented.map_affineSectionsIso_pointsEquiv
    (GeneralLinear.functor (Index l) (CommRingCat.of K))
    (GeneralLinear.corepresentableBy (Index l) (CommRingCat.of K)) A
    (z ≫ (inclusion K).hom.hom)
  change Matrix.GeneralLinearGroup.map (Corepresented.affineSectionsIso A).hom.hom.toRingHom
    (GeneralLinear.pointsEquiv (Index l) (CommRingCat.of K)
      ((algSpec (CommRingCat.of K)).obj (op A)) (z ≫ (inclusion K).hom.hom)) =
        GeneralLinear.affinePointsEquiv (Index l) (CommRingCat.of K) A
          (z ≫ (inclusion K).hom.hom) at h
  rw [← h, pointsEquiv_inclusion]
  apply Units.ext
  exact (affineMatrix_val_eq_ambientMatrix_map K A z).symm

/-- The standard representation supplies the linear differential. -/
def lieMatrix : Additive (lieKernel (groupScheme l K) K) →ₗ[K]
    Matrix (Index l) (Index l) K := (inclusion K).kernelDifferential K

/-- The differential agrees with the unique epsilon coefficient of the actual point. -/
theorem lieMatrix_eq_tangentCoefficient (x : Additive (lieKernel (groupScheme l K) K)) :
    lieMatrix K x = tangentCoefficient K x.toMul := by
  change coefficients (GeneralLinear.affinePointsEquiv (Index l) (CommRingCat.of K) 𝔻
    (x.toMul.val ≫ (inclusion K).hom.hom)) = coefficients (affineMatrix K 𝔻 x.toMul.val)
  rw [affinePointsEquiv_inclusion]

/-- The actual differential is injective. -/
theorem lieMatrix_injective : Function.Injective (lieMatrix (l := l) K) :=
  (pointKernelLinearEquiv (n := Index l) (R := CommRingCat.of K) (A := K)).symm.injective.comp
    (Lie.targetMapLinear_injective (inclusion K) K)

/-- The image of the actual Lie differential is exactly the linearized norm-one equations. -/
theorem range_lieMatrix : LinearMap.range (lieMatrix (l := l) K) = lieMatrices := by
  ext Y
  constructor
  · rintro ⟨x, rfl⟩
    rw [lieMatrix_eq_tangentCoefficient]
    exact tangentCoefficient_mem K _
  · intro hY
    refine ⟨Additive.ofMul (tangentKernelMap K (Multiplicative.ofAdd ⟨Y, hY⟩)), ?_⟩
    rw [lieMatrix_eq_tangentCoefficient]
    change coefficients (affineMatrix K 𝔻 (tangentKernelMap K (Multiplicative.ofAdd ⟨Y, hY⟩)).val) = Y
    rw [affineMatrix_tangentKernelMap, coefficients_matrixUnit]
    rfl

/-- The tangent coefficient equations give linear coordinates on the actual
Library Lie module, including its actual epsilon-scaling action. -/
def lieMatrixEquiv : Additive (lieKernel (groupScheme l K) K) ≃ₗ[K]
    lieMatrices (l := l) (K := K) :=
  (LinearEquiv.ofInjective (lieMatrix K) (lieMatrix_injective K)).trans
    (LinearEquiv.ofEq _ _ (range_lieMatrix K))

end Langlands.GroupScheme.OddOrthogonalMatrix
