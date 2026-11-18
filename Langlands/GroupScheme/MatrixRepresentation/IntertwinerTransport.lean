import Langlands.GroupScheme.MatrixRepresentation.ScalarExtensionCoordinates
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.GroupScheme.Lie.PrimePowerFieldExtension

/-! # Scalar extension of intertwiners and transport of actual representation coordinates -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section BaseChange

variable {k K : Type u} [CommRing k] [CommRing K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The actual affine base-change matrix comparison for an arbitrary finite coordinate type. -/
theorem affineMatrix_baseChange_fintype (ρ : MatrixRepresentation G n)
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (x : Lie.AffinePoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) A) :
    ((ρ.baseChange (algebraBaseMap k K)).affineMatrix (CommAlgCat.of (CommRingCat.of K) A) x :
        Matrix n n A) =
      ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A)
        (Lie.affineBaseChangeEquiv k K G A x) := by
  have h₁ := ρ.pointMatrix_baseChange (algebraBaseMap k K)
    ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of (CommRingCat.of K) A))) x
  have h₂ := ρ.pointMatrix_naturality (Lie.affineBaseTestIso k K A).inv
    (GroupScheme.baseChangePointsEquiv (algebraBaseMap k K) G _ x)
  rw [pointMatrix_eq_affineMatrix] at h₁ h₂
  rw [← h₁] at h₂
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1
  ext i j
  apply hinj
  have h := congrArg (fun M => M.1 i j) h₂
  exact h.symm

end BaseChange

section Intertwiners

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- A bijective intertwiner stays bijective after arbitrary field extension. -/
theorem Intertwines.baseChange_bijective {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {C : Matrix m n k} (hC : ρ.Intertwines σ C)
    (hbij : Function.Bijective C.mulVecLin) :
    (ρ.baseChange (algebraBaseMap k K)).Intertwines
        (σ.baseChange (algebraBaseMap k K)) (C.map (algebraMap k K)) ∧
      Function.Bijective (C.map (algebraMap k K)).mulVecLin :=
  ⟨hC.baseChange, Lie.mulVecLin_map_injective C hbij.1,
    Lie.mulVecLin_map_surjective C hbij.2⟩

end Intertwiners

section Coordinates

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The coordinate matrices of a linear equivalence and its inverse multiply to the identity. -/
theorem toMatrix_linearEquiv_mul_symm (e : (n → k) ≃ₗ[k] (m → k)) :
    LinearMap.toMatrix' e.toLinearMap * LinearMap.toMatrix' e.symm.toLinearMap = 1 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', Matrix.toLin'_one]
  exact LinearMap.ext fun v => e.apply_symm_apply v

/-- The inverse coordinate matrix is also a left inverse of the coordinate matrix. -/
theorem toMatrix_linearEquiv_symm_mul (e : (n → k) ≃ₗ[k] (m → k)) :
    LinearMap.toMatrix' e.symm.toLinearMap * LinearMap.toMatrix' e.toLinearMap = 1 := by
  simpa only [LinearEquiv.symm_symm] using toMatrix_linearEquiv_mul_symm e.symm

/-- An invertible change of coordinates is invariant on every scheme test. -/
theorem isStableCoordinates_linearEquiv (ρ : MatrixRepresentation G n)
    (e : (n → k) ≃ₗ[k] (m → k)) :
    ρ.IsStableCoordinates (LinearMap.toMatrix' e.symm.toLinearMap)
      (LinearMap.toMatrix' e.toLinearMap) := by
  intro T x
  have hBC := toMatrix_linearEquiv_symm_mul e
  have hmap := congrArg (fun M => M.map (scalarMap T)) hBC
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at hmap
  change _ = (LinearMap.toMatrix' e.symm.toLinearMap).map (scalarMap T) *
    ((LinearMap.toMatrix' e.toLinearMap).map (scalarMap T) *
      (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *
      (LinearMap.toMatrix' e.symm.toLinearMap).map (scalarMap T))
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hmap, Matrix.one_mul]

/-- Transport an actual group-scheme representation along a supplied linear equivalence. -/
def transportCoordinates (ρ : MatrixRepresentation G n)
    (e : (n → k) ≃ₗ[k] (m → k)) : MatrixRepresentation G m :=
  restrictCoordinates ρ (LinearMap.toMatrix' e.symm.toLinearMap)
    (LinearMap.toMatrix' e.toLinearMap) (toMatrix_linearEquiv_mul_symm e)
    (isStableCoordinates_linearEquiv ρ e)

/-- The inverse coordinate equivalence intertwines the transported and original actions. -/
theorem intertwines_transportCoordinates_symm (ρ : MatrixRepresentation G n)
    (e : (n → k) ≃ₗ[k] (m → k)) :
    (ρ.transportCoordinates e).Intertwines ρ (LinearMap.toMatrix' e.symm.toLinearMap) :=
  intertwines_restrictCoordinates ρ _ _ _ _

/-- The coordinate equivalence itself is a bijective intertwiner into the transported action. -/
theorem intertwines_transportCoordinates (ρ : MatrixRepresentation G n)
    (e : (n → k) ≃ₗ[k] (m → k)) :
    ρ.Intertwines (ρ.transportCoordinates e) (LinearMap.toMatrix' e.toLinearMap) ∧
      Function.Bijective (LinearMap.toMatrix' e.toLinearMap).mulVecLin := by
  have hi : Function.Injective (LinearMap.toMatrix' e.symm.toLinearMap).mulVecLin := by
    change Function.Injective (Matrix.toLin' (LinearMap.toMatrix' e.symm.toLinearMap))
    rw [Matrix.toLin'_toMatrix']
    exact e.symm.injective
  refine ⟨Intertwines.of_comp_injective (intertwines_transportCoordinates_symm ρ e) hi ?_, ?_⟩
  · rw [toMatrix_linearEquiv_symm_mul e]
    intro A x
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
  · change Function.Bijective (Matrix.toLin' (LinearMap.toMatrix' e.toLinearMap))
    rw [Matrix.toLin'_toMatrix']
    exact e.bijective

end Coordinates
end Langlands.GroupScheme.MatrixRepresentation
