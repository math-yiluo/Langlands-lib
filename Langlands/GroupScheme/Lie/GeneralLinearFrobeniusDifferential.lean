import Langlands.GroupScheme.GeneralLinearFrobenius
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Lie.GeneralLinearAdjoint

/-! # The differential of matrix Frobenius vanishes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.GeneralLinear

variable (k : Type u) [Field k] (p : ℕ) [ExpChar k p]

/-- Positive-characteristic Frobenius kills every pure epsilon element, even over
the zero test algebra. -/
theorem algebraFrobenius_inr (hp : 1 < p)
    (A : Type u) [CommRing A] [Algebra k A] (a : A) :
    algebraFrobenius k p (DualNumber A) (TrivSqZeroExt.inr a) = 0 := by
  apply pow_eq_zero_of_le hp
  rw [pow_two, TrivSqZeroExt.inr_mul_inr]

variable (n : Type) [Fintype n] [DecidableEq n]

local instance : IsAffineHom (groupScheme n (CommRingCat.of k)).X.hom :=
  isAffineHom_groupScheme n (CommRingCat.of k)

/-- Entrywise Frobenius sends every matrix `I + εX` to the identity. -/
theorem frobeniusPoints_matrixUnit (hp : 1 < p)
    (A : Type u) [CommRing A] [Algebra k A] (X : Matrix n n A) :
    frobeniusPoints k p n (DualNumber A) (DualNumber.matrixUnit X) = 1 := by
  apply Units.ext
  change (algebraFrobenius k p (DualNumber A)).mapMatrix
    (1 + DualNumber.epsilonMatrix X) = 1
  rw [map_add, map_one]
  suffices h : (algebraFrobenius k p (DualNumber A)).mapMatrix
      (DualNumber.epsilonMatrix X) = 0 by rw [h, add_zero]
  apply Matrix.ext
  intro i j
  exact algebraFrobenius_inr k p hp A (X i j)

/-- The actual matrix Frobenius homomorphism kills every dual-number identity
kernel, on every test algebra. -/
theorem targetMap_frobeniusHom (hp : 1 < p)
    (A : Type u) [CommRing A] [Algebra k A]
    (X : lieKernel (groupScheme n (CommRingCat.of k)) A) :
    Lie.targetMap (frobeniusHom k p n) A X = 1 := by
  obtain ⟨M, rfl⟩ :=
    (DualNumber.pointKernelEquiv (n := n) (R := CommRingCat.of k) (S := A)).surjective X
  apply Subtype.ext
  apply (affinePointsEquiv n (CommRingCat.of k)
    (CommAlgCat.of (CommRingCat.of k) (DualNumber A))).injective
  change affinePointsEquiv n (CommRingCat.of k) _
    (DualNumber.pointUnit M ≫ (frobeniusHom k p n).hom.hom) =
      affinePointsEquiv n (CommRingCat.of k) _ 1
  rw [affinePointsEquiv_frobeniusHom, DualNumber.pointUnit_matrix, map_one]
  exact frobeniusPoints_matrixUnit k p n hp A M

/-- The actual linear differential of positive-characteristic matrix Frobenius
is zero on every test algebra. -/
theorem targetMapLinear_frobeniusHom (hp : 1 < p)
    (A : Type u) [CommRing A] [Algebra k A] :
    Lie.targetMapLinear (frobeniusHom k p n) A = 0 := by
  apply DFunLike.ext
  intro X
  apply Additive.toMul.injective
  exact targetMap_frobeniusHom k p n hp A X.toMul

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.GroupScheme

local instance (k : Type u) [Field k] (n : Type) [Fintype n] [DecidableEq n] :
    IsAffineHom (GeneralLinear.groupScheme n (CommRingCat.of k)).X.hom :=
  GeneralLinear.isAffineHom_groupScheme n (CommRingCat.of k)

/-- Positive-characteristic matrix Frobenius has zero actual differential over
every field and on every algebra over that field. -/
def GeneralLinearFrobeniusDifferentialStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [ExpChar k p], 1 < p →
    ∀ (n : Type) [Fintype n] [DecidableEq n]
      (A : Type u) [CommRing A] [Algebra k A],
      Lie.targetMapLinear (GeneralLinear.frobeniusHom k p n) A = 0

theorem generalLinearFrobeniusDifferential :
    GeneralLinearFrobeniusDifferentialStatement.{u} := by
  intro k _ p _ hp n _ _ A _ _
  exact GeneralLinear.targetMapLinear_frobeniusHom k p n hp A

end Langlands.GroupScheme
