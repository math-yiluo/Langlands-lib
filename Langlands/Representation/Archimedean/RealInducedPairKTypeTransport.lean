import Langlands.Representation.Archimedean.RealKTypeTransport

/-!
# Compact transport for two real induction blocks

The permutation of the two coordinate planes identifies the `O(4)`-finite
functions of the standard modules of `[induced d, induced e]` and
`[induced e, induced d]`. Consequently an injective `O(4)`-equivariant map
between these spaces is surjective.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace RealInducedPairKTypeTransport

open RealKTypeTransport PrincipalSeriesExtension GramFormula

/-- The permutation interchanging the ordered coordinate planes `(0,1)` and `(2,3)`. -/
def swapMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

theorem swapMatrix_mem : swapMatrix ∈ Matrix.unitaryGroup (Fin 4) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMatrix, Matrix.mul_apply, Fin.sum_univ_four]

/-- The coordinate-plane permutation as an element of `O(4)`. -/
def swap : Matrix.unitaryGroup (Fin 4) ℝ := ⟨swapMatrix, swapMatrix_mem⟩

theorem swap_mul_swap : swap * swap = 1 := by
  apply Subtype.ext
  change swapMatrix * swapMatrix = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMatrix, Matrix.mul_apply, Fin.sum_univ_four]

theorem swap_mul_blockRotation_zero (θ : ℝ) :
    (swap : Matrix (Fin 4) (Fin 4) ℝ) *
        (blockRotation 4 0 θ : Matrix (Fin 4) (Fin 4) ℝ) =
      (blockRotation 4 2 θ : Matrix (Fin 4) (Fin 4) ℝ) *
        (swap : Matrix (Fin 4) (Fin 4) ℝ) := by
  change swapMatrix * _ = _ * swapMatrix
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [RealBlockRotation.blockRotation_apply (by norm_num : 0 + 1 < 4),
    RealBlockRotation.blockRotation_apply (by norm_num : 2 + 1 < 4)]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four, swapMatrix]

theorem swap_mul_blockRotation_two (θ : ℝ) :
    (swap : Matrix (Fin 4) (Fin 4) ℝ) *
        (blockRotation 4 2 θ : Matrix (Fin 4) (Fin 4) ℝ) =
      (blockRotation 4 0 θ : Matrix (Fin 4) (Fin 4) ℝ) *
        (swap : Matrix (Fin 4) (Fin 4) ℝ) := by
  change swapMatrix * _ = _ * swapMatrix
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [RealBlockRotation.blockRotation_apply (by norm_num : 0 + 1 < 4),
    RealBlockRotation.blockRotation_apply (by norm_num : 2 + 1 < 4)]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four, swapMatrix]

variable (d e : ComplexCharacterData)

theorem swap_isSignCompatible :
    IsSignCompatible swap
      (realPositionCharacter [RealBlock.induced d, RealBlock.induced e])
      (realPositionCharacter [RealBlock.induced e, RealBlock.induced d]) := by
  intro a
  refine ⟨![a 2, a 3, a 0, a 1], ?_, ?_⟩
  · apply Subtype.ext
    change swapMatrix * Matrix.diagonal _ = Matrix.diagonal _ * swapMatrix
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swapMatrix, Matrix.mul_apply, Matrix.diagonal]
  · rw [JacquetKernel.principalSeriesCharacter_sign,
      JacquetKernel.principalSeriesCharacter_sign, Fin.prod_univ_four, Fin.prod_univ_four]
    simp [realPositionCharacter]
    ring

theorem swap_landing :
    ∀ f ∈ kFiniteFunctions
        (realStandardModule 4 [RealBlock.induced d, RealBlock.induced e])
        (unitaryCompact ℝ 4),
      extension (shiftedExponent 4
          (realPositionExponent [RealBlock.induced e, RealBlock.induced d]))
          (transport swap f) ∈
        kFiniteFunctions
          (realStandardModule 4 [RealBlock.induced e, RealBlock.induced d])
          (unitaryCompact ℝ 4) := by
  intro f hf
  have hE := extension_transport_mem (realStandardModule_le_principalSeries _ _)
    (swap_isSignCompatible d e) (realPositionCharacter_eq_signUnit_mul _) hf
  refine Submodule.mem_inf.mpr ⟨mem_realStandardModule_of_unitaryCompact (n := 4) rfl
    (Submodule.mem_inf.mp hE).1 ?_, (Submodule.mem_inf.mp hE).2⟩
  have hg : ∀ κ : Matrix.unitaryGroup (Fin 4) ℝ,
      extension (shiftedExponent 4
          (realPositionExponent [RealBlock.induced e, RealBlock.induced d]))
          (transport swap f) (Unitary.toUnits κ) = f (Unitary.toUnits (swap * κ)) :=
    fun κ => extension_unitary _ _ κ
  intro p d' hd j hj k hk
  rcases p with _ | _ | _ | _ | p
  · simp only [realInducedBlockAt, Option.some.injEq] at hd
    subst hd
    rw [blockFourierCoefficient_of_transport hg swap_mul_blockRotation_zero j hk]
    exact (Submodule.mem_inf.mp hf).1.2 2 e (by simp [realInducedBlockAt]) j hj _
  · simp [realInducedBlockAt] at hd
  · simp only [realInducedBlockAt, Option.some.injEq] at hd
    subst hd
    rw [blockFourierCoefficient_of_transport hg swap_mul_blockRotation_two j hk]
    exact (Submodule.mem_inf.mp hf).1.2 0 d (by simp [realInducedBlockAt]) j hj _
  all_goals simp [realInducedBlockAt] at hd

/-- Compact transport from `[induced d, induced e]` to `[induced e, induced d]`. -/
def swapMap :
    kFiniteFunctions (realStandardModule 4 [RealBlock.induced d, RealBlock.induced e])
        (unitaryCompact ℝ 4) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule 4 [RealBlock.induced e, RealBlock.induced d])
        (unitaryCompact ℝ 4) :=
  transportMap _ _ swap _ (swap_landing d e)

theorem swapMap_apply_toUnits
    (f : kFiniteFunctions
      (realStandardModule 4 [RealBlock.induced d, RealBlock.induced e]) (unitaryCompact ℝ 4))
    (κ : Matrix.unitaryGroup (Fin 4) ℝ) :
    (swapMap d e f : Langlands.GeneralLinear 4 ℝ → ℂ) (Unitary.toUnits κ) =
      (f : Langlands.GeneralLinear 4 ℝ → ℂ) (Unitary.toUnits (swap * κ)) :=
  transportMap_apply_toUnits f κ

theorem swapMap_injective : Function.Injective (swapMap d e) :=
  transportMap_injective (realStandardModule_le_principalSeries _ _)

theorem swapMap_isRealKEquivariant : IsRealKEquivariant _ _ (swapMap d e) :=
  transportMap_isRealKEquivariant (realStandardModule_le_principalSeries _ _)
    (fun _ hk _ hf => rightTranslation_mem_kFiniteFunctions_realStandardModule 4 _ hf hk)
    (swap_isSignCompatible d e) (realPositionCharacter_eq_signUnit_mul _)

theorem swapMap_swapMap
    (f : kFiniteFunctions
      (realStandardModule 4 [RealBlock.induced d, RealBlock.induced e]) (unitaryCompact ℝ 4)) :
    swapMap e d (swapMap d e f) = f := by
  apply RealKTypeCount.restrict_injective (realStandardModule_le_principalSeries _ _)
  funext κ
  change (swapMap e d (swapMap d e f) : Langlands.GeneralLinear 4 ℝ → ℂ)
      (Unitary.toUnits κ) = (f : Langlands.GeneralLinear 4 ℝ → ℂ) (Unitary.toUnits κ)
  rw [swapMap_apply_toUnits, swapMap_apply_toUnits, ← mul_assoc, swap_mul_swap, one_mul]

theorem swapMap_surjective : Function.Surjective (swapMap d e) :=
  fun f => ⟨swapMap e d f, swapMap_swapMap e d f⟩

/-- Every injective `O(4)`-equivariant map between the two block orders is surjective. -/
theorem surjective_of_injective
    {T : kFiniteFunctions
        (realStandardModule 4 [RealBlock.induced d, RealBlock.induced e])
        (unitaryCompact ℝ 4) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule 4 [RealBlock.induced e, RealBlock.induced d])
        (unitaryCompact ℝ 4)}
    (hT : IsRealKEquivariant _ _ T) (hTi : Function.Injective T) :
    Function.Surjective T :=
  RealKTypeCount.surjective_of_injective (realStandardModule_le_principalSeries _ _)
    (realStandardModule_le_principalSeries _ _) hT hTi
    (swapMap_isRealKEquivariant e d) (swapMap_injective e d)

end RealInducedPairKTypeTransport

end Langlands.Archimedean
