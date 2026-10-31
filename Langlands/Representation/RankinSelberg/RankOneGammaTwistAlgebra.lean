import Langlands.Representation.RankinSelberg.RankOneGammaTwistStatement
import Langlands.Representation.RankinSelberg.TwistInvariance
import Langlands.Representation.Whittaker.AlgebraicTwist
import Langlands.Representation.RankinSelberg.RankOneQuotient

noncomputable section

namespace Langlands.RankinSelberg.RankOneGammaTwist

open Whittaker GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV

section Determinants

variable {F : Type uF} [Field F]

/-- Expansion along the first row of the actual long Weyl matrix. -/
theorem determinant_weylLong_succ (n : ℕ) :
    determinant (weylLong (n + 1) F) = (-1 : Fˣ) ^ n * determinant (weylLong n F) := by
  apply Units.ext
  change Matrix.det (weylLong (n + 1) F).val =
    (-1 : F) ^ n * Matrix.det (weylLong n F).val
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last n)]
  · have hminor : (weylLong (n + 1) F).val.submatrix Fin.succ (Fin.last n).succAbove =
        (weylLong n F).val := by
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_last, weylLong_entry,
        Fin.rev_castSucc, Fin.succ_inj]
    rw [hminor]
    simp [weylLong_entry]
  · intro j _ hj
    have hrev : j.rev ≠ 0 := by
      intro h
      apply hj
      apply Fin.rev_injective
      simpa using h
    simp [weylLong_entry, hrev]
  · simp

@[simp] theorem weylLong_one : weylLong 1 F = 1 := by
  apply Units.ext
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  simp [weylLong_entry]

theorem determinant_inverseTranspose {m : ℕ} (g : Langlands.GeneralLinear m F) :
    determinant (inverseTranspose m F g) = (determinant g)⁻¹ := by
  apply Units.ext
  change Matrix.det ((g⁻¹).val.transpose) = _
  rw [Matrix.det_transpose]
  exact congrArg Units.val (map_inv determinant g)

theorem determinant_blockWeyl (r : ℕ) (hr : 0 < r) :
    determinant (blockWeylAt (F := F) 0 r hr) = determinant (weylLong r F) := by
  apply Units.ext
  change Matrix.det (Matrix.reindex _ _ (blockSum ((1 : Langlands.GeneralLinear 1 F),
    weylLong (r - 0) F)).val) = _
  rw [Matrix.det_reindex_self]
  change Matrix.det (Matrix.reindex _ _ (Matrix.fromBlocks
    (1 : Langlands.GeneralLinear 1 F).val 0 0 (weylLong (r - 0) F).val)) = _
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Units.val_one,
    Matrix.det_one, one_mul]
  rfl

/-- The two actual Weyl factors leave precisely the rank-one sign. -/
theorem determinant_dual_argument (r : ℕ) (hr : 0 < r)
    (g : Langlands.GeneralLinear (r + 1) F) :
    determinant (weylLong (r + 1) F * inverseTranspose (r + 1) F
      (g * blockWeylAt 0 r hr)) = (-1 : Fˣ) ^ r * (determinant g)⁻¹ := by
  rw [map_mul, determinant_inverseTranspose, map_mul, determinant_blockWeyl,
    determinant_weylLong_succ]
  simp only [mul_inv_rev]
  group

theorem character_negOne_sq (χ : Fˣ →* ℂˣ) : χ (-1) ^ 2 = 1 := by
  rw [← map_pow]
  simp

end Determinants

section Models

variable {F : Type uF} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ)
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- The candidate functional retains its underlying linear map. -/
abbrev candidateFunctional (ℓ : glFunctionals ψ n π) :=
  twistFunctional _ _ (χ.comp determinant) (determinantCharacter_unipotent χ) π ℓ

/-- Every linear form on the rank-one test is an inverse functional. -/
def testFunctional (η : Fˣ →* ℂˣ) (ellC : ℂ →ₗ[ℂ] ℂ) :
    glInverseFunctionals ψ 0 (rankOneCharacter η) :=
  ⟨ellC, by
    intro u z
    have : Subsingleton (upperUnipotent (0 + 1) F) := upperUnipotent_one_subsingleton
    obtain rfl : u = 1 := Subsingleton.elim _ _
    simp⟩

@[simp] theorem test_coefficient (η : Fˣ →* ℂˣ) (ellC : ℂ →ₗ[ℂ] ℂ)
    (z : ℂ) (g : Langlands.GeneralLinear 1 F) :
    (modelMap (rankOneCharacter η) (testFunctional ψ η ellC) z).val.val g =
      (η (determinant g) : ℂ) * ellC z := by
  change ellC ((η (determinant g) : ℂ) • z) = _
  exact ellC.map_smul (η (determinant g) : ℂ) z

@[simp] theorem candidate_coefficient (ℓ : glFunctionals ψ n π) (v : V)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (modelMap (Langlands.twist (χ.comp determinant) π)
      (candidateFunctional ψ χ π ℓ) v).val.val g =
      (χ (determinant g) : ℂ) * (modelMap π ℓ v).val.val g := by
  exact (congrFun (twistFunction_coefficient _ _ (χ.comp determinant)
    (determinantCharacter_unipotent χ) π ℓ v) g).symm

/-- The scalar is computed on the actual test coefficient image. -/
theorem test_minusOne (η : Fˣ →* ℂˣ) (ellC : ℂ →ₗ[ℂ] ℂ) :
    HasModelMinusOneScalar (rankOneCharacter η) (testFunctional ψ η ellC) (η (-1)) := by
  intro f g
  obtain ⟨z, rfl⟩ := modelMap_surjective (rankOneCharacter η) (testFunctional ψ η ellC) f
  rw [test_coefficient, test_coefficient, map_mul, map_mul, Units.val_mul]
  have hd : determinant (-1 : Langlands.GeneralLinear 1 F) = -1 := by
    apply Units.ext
    change Matrix.det (-1 : Matrix (Fin 1) (Fin 1) F) = (-1 : F)
    simp [Matrix.det_unique]
  rw [hd, mul_assoc]

end Models

end Langlands.RankinSelberg.RankOneGammaTwist
