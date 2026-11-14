import Langlands.GroupScheme.VectorScalarKernel
import Langlands.GroupScheme.Rational.VectorCoordinateRealization
import Langlands.GroupScheme.KernelRepresentativeTransport
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Diagonal vector maps and their actual scheme kernels -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Classical
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.VectorGroup

variable {R : CommRingCat.{u}} {n : ℕ}

/-- Scale each coordinate by its own coefficient on every scheme test. -/
def diagonalPoints (c : Fin n → R) (T : Over (Spec R)) :
    (T ⟶ (groupScheme R n).X) →* (T ⟶ (groupScheme R n).X) where
  toFun x := (coordinates R n T).symm
    (Multiplicative.ofAdd fun j => scalarMap T (c j) * (coordinates R n T x).toAdd j)
  map_one' := by
    apply (coordinates R n T).injective
    apply Multiplicative.toAdd.injective
    funext j
    simp only [MulEquiv.apply_symm_apply, map_one]
    exact mul_zero _
  map_mul' x y := by
    apply (coordinates R n T).injective
    apply Multiplicative.toAdd.injective
    funext j
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact mul_add _ _ _

@[simp]
theorem diagonalPoints_coord (c : Fin n → R) (T : Over (Spec R))
    (x : T ⟶ (groupScheme R n).X) (j : Fin n) :
    (coordinates R n T (diagonalPoints c T x)).toAdd j =
      scalarMap T (c j) * (coordinates R n T x).toAdd j :=
  congrArg (fun y => y.toAdd j) ((coordinates R n T).apply_symm_apply _)

theorem diagonalPoints_natural (c : Fin n → R) {T W : Over (Spec R)}
    (f : W ⟶ T) (x : T ⟶ (groupScheme R n).X) :
    diagonalPoints c W (f ≫ x) = f ≫ diagonalPoints c T x := by
  apply points_ext
  intro j
  rw [diagonalPoints_coord, coordinates_comp, coordinates_comp]
  dsimp only
  rw [diagonalPoints_coord, map_mul]
  exact congrArg (fun a => a * f.left.appTop.hom ((coordinates R n T x).toAdd j))
    (congrArg (fun g : R →+* Γ(W.left, ⊤) => g (c j)) (coefficientMap_comp f)).symm

/-- The diagonal endomorphism of the polynomial vector group. -/
def diagonal (c : Fin n → R) : groupScheme R n ⟶ groupScheme R n :=
  homOfPoints (diagonalPoints c) (diagonalPoints_natural c)

@[simp]
theorem coordinates_diagonal (c : Fin n → R) (T : Over (Spec R))
    (x : T ⟶ (groupScheme R n).X) (j : Fin n) :
    (coordinates R n T (x ≫ (diagonal c).hom.hom)).toAdd j =
      scalarMap T (c j) * (coordinates R n T x).toAdd j := by
  rw [diagonal, comp_homOfPoints, diagonalPoints_coord]

/-- Constant diagonal coefficients recover the existing scalar map. -/
theorem diagonal_const (c : R) :
    diagonal (n := n) (fun _ => c) = scalar c := by
  apply hom_ext_points
  intro T x
  apply points_ext
  intro j
  rw [coordinates_diagonal, coordinates_scalar]

@[simp]
theorem diagonal_one : diagonal (R := R) (n := n) 1 = 𝟙 _ := by
  rw [show (1 : Fin n → R) = fun _ => (1 : R) from rfl, diagonal_const, scalar_one]

theorem diagonal_comp (c d : Fin n → R) :
    diagonal c ≫ diagonal d = diagonal (c * d) := by
  apply hom_ext_points
  intro T x
  apply points_ext
  intro j
  rw [Grp.comp_hom_hom, ← Category.assoc, coordinates_diagonal,
    coordinates_diagonal, coordinates_diagonal, Pi.mul_apply, map_mul]
  ring

/-- Coordinatewise multiplication by units is an actual group-scheme isomorphism. -/
def diagonalIso (c : Fin n → Rˣ) : groupScheme R n ≅ groupScheme R n where
  hom := diagonal fun j => (c j : R)
  inv := diagonal fun j => ((c j)⁻¹ : Rˣ)
  hom_inv_id := by
    rw [diagonal_comp, show
      (fun j => (c j : R)) * (fun j => (((c j)⁻¹ : Rˣ) : R)) = 1 by
        funext j
        exact Units.mul_inv (c j), diagonal_one]
  inv_hom_id := by
    rw [diagonal_comp, show
      (fun j => (((c j)⁻¹ : Rˣ) : R)) * (fun j => (c j : R)) = 1 by
        funext j
        exact Units.inv_mul (c j), diagonal_one]

section BaseChange

variable {A : CommRingCat.{u}} (ρ : R ⟶ A)

/-- The diagonal map commutes with actual base change, coordinate by coordinate. -/
theorem diagonal_baseChange (c : Fin n → R) :
    (baseChangeIso (n := n) ρ).hom ≫ diagonal (fun j => ρ.hom (c j)) =
      (GroupScheme.baseChange (Spec.map ρ)).map (diagonal c) ≫
        (baseChangeIso ρ).hom := by
  apply hom_ext_points
  intro T x
  apply points_ext
  intro j
  simp only [Grp.comp_hom_hom, ← Category.assoc, coordinates_diagonal,
    coordinates_baseChangeIso_hom]
  change scalarMap T (ρ.hom (c j)) *
      (baseChangeCoordinates ρ T x).toAdd j =
    (coordinates R n ((Over.map (Spec.map ρ)).obj T)
      (baseChangePointsEquiv (Spec.map ρ) (groupScheme R n) T
        (x ≫ ((GroupScheme.baseChange (Spec.map ρ)).map (diagonal c)).hom.hom))).toAdd j
  rw [baseChangePointsEquiv_comp, coordinates_diagonal, coefficientMap_map]
  rfl

end BaseChange

section Field

variable {k : Type u} [Field k] (c : Fin n → k)

/-- On every scheme test, the killed coordinates are precisely the coordinates whose
coefficient is nonzero. The test scheme need not be reduced or affine. -/
theorem diagonal_comp_eq_one_iff (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (groupScheme (CommRingCat.of k) n).X) :
    x ≫ (diagonal (R := CommRingCat.of k) c).hom.hom = 1 ↔
      ∀ j, c j ≠ 0 → (coordinates (CommRingCat.of k) n T x).toAdd j = 0 := by
  constructor
  · intro hx j hj
    have h := congrArg (fun y => (coordinates (CommRingCat.of k) n T y).toAdd j) hx
    rw [coordinates_diagonal, map_one] at h
    exact (((isUnit_iff_ne_zero.mpr hj).map (scalarMap T)).mul_right_eq_zero).mp h
  · intro hx
    apply points_ext
    intro j
    rw [coordinates_diagonal, map_one]
    change scalarMap T (c j) * (coordinates (CommRingCat.of k) n T x).toAdd j = 0
    by_cases hj : c j = 0
    · rw [hj, map_zero, zero_mul]
    · rw [hx j hj, mul_zero]

/-- The actual kernel inclusion represents the zero-coefficient coordinate block. -/
theorem range_kernelι_diagonal :
    SubgroupFunctor.range (kernelι (diagonal (R := CommRingCat.of k) c)) =
      RelativeRoot.vectorCoordinateSubgroup (coordinates (CommRingCat.of k) n)
        isNaturalVectorCoordinates {j | c j = 0} := by
  ext T x
  rw [mem_range_kernelι_iff, diagonal_comp_eq_one_iff]
  rfl

/-- The coordinate block on the indices whose coefficients vanish. -/
def diagonalKernelInclusion :
    groupScheme (CommRingCat.of k) (Fintype.card {j : Fin n // c j = 0}) ⟶
      groupScheme (CommRingCat.of k) n := by
  classical
  exact RelativeRoot.vectorCoordinateBlockInclusion (coordinates (CommRingCat.of k) n)
    {j | c j = 0} (Fintype.equivFin {j : Fin n // c j = 0}).symm
    isNaturalVectorCoordinates

theorem mono_diagonalKernelInclusion : Mono (diagonalKernelInclusion c).hom.hom := by
  classical
  exact RelativeRoot.mono_vectorCoordinateBlockInclusion _ _ _ isNaturalVectorCoordinates

theorem range_kernelι_diagonal_eq_range :
    SubgroupFunctor.range (kernelι (diagonal (R := CommRingCat.of k) c)) =
      SubgroupFunctor.range (diagonalKernelInclusion c) := by
  classical
  rw [range_kernelι_diagonal]
  exact (RelativeRoot.isRepresentedBy_vectorCoordinateBlockInclusion _ _ _
    isNaturalVectorCoordinates).2.symm

/-- The full scheme-theoretic kernel is a vector group, of dimension the number of
zero coefficients. This is an isomorphism of group schemes over the original field. -/
def diagonalKernelIso :
    kernel (diagonal (R := CommRingCat.of k) c) ≅
      groupScheme (CommRingCat.of k) (Fintype.card {j : Fin n // c j = 0}) := by
  have : Mono (diagonalKernelInclusion c).hom.hom := mono_diagonalKernelInclusion c
  exact KernelRepresentative.iso (diagonal (R := CommRingCat.of k) c) (diagonalKernelInclusion c)
    (range_kernelι_diagonal_eq_range c)

@[reassoc]
theorem diagonalKernelIso_hom_comp :
    (diagonalKernelIso c).hom ≫ diagonalKernelInclusion c = kernelι (diagonal (R := CommRingCat.of k) c) := by
  have : Mono (diagonalKernelInclusion c).hom.hom := mono_diagonalKernelInclusion c
  exact KernelRepresentative.iso_hom_comp _ _ (range_kernelι_diagonal_eq_range c)

/-- Diagonal vector maps over a field have smooth connected unipotent actual kernels. -/
theorem diagonal_kernel_properties :
    Smooth (kernel (diagonal (R := CommRingCat.of k) c)).X.hom ∧
      ConnectedSpace (kernel (diagonal (R := CommRingCat.of k) c)).X.left ∧
        IsUnipotent (kernel (diagonal (R := CommRingCat.of k) c)) := by
  let m := Fintype.card {j : Fin n // c j = 0}
  let hv : RelativeRoot.IsVectorGroupOfDimension
      (groupScheme (CommRingCat.of k) m) m :=
    ⟨coordinates (CommRingCat.of k) m, isNaturalVectorCoordinates⟩
  exact smooth_connected_unipotent_of_groupIso (diagonalKernelIso c)
    ⟨hv.smooth, hv.connectedSpace, isUnipotent k m⟩

/-- Ring-to-field specialization allows independently vanishing coordinate coefficients. -/
theorem diagonal_baseChange_kernel_properties {R : CommRingCat.{u}}
    (ρ : R ⟶ CommRingCat.of k) (d : Fin n → R) :
    Smooth (kernel ((GroupScheme.baseChange (Spec.map ρ)).map (diagonal d))).X.hom ∧
      ConnectedSpace
        (kernel ((GroupScheme.baseChange (Spec.map ρ)).map (diagonal d))).X.left ∧
      IsUnipotent (kernel ((GroupScheme.baseChange (Spec.map ρ)).map (diagonal d))) := by
  exact smooth_connected_unipotent_of_groupIso
    (kernelSquareIso _ _ (baseChangeIso ρ) (baseChangeIso ρ)
      (diagonal_baseChange ρ d)) (diagonal_kernel_properties (fun j => ρ.hom (d j)))

end Field

end Langlands.GroupScheme.VectorGroup
