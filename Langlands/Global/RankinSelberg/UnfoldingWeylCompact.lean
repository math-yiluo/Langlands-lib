import Langlands.Global.RankinSelberg.WhittakerIntegrals
import Langlands.Global.AdelicGLStandardCompact
import Langlands.Group.GL.Maps

/-! # The unfolding Weyl representative lies in the standard compact subgroup -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Global

local instance weylCompactSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

section PermutationMatrices

variable {R : Type*} [CommRing R] {a b n m : ℕ}

/-- The permutation acting separately on the two consecutive blocks. -/
def gaugeBlockPermutation (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) :
    Equiv.Perm (Fin (a + b)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr σ τ)).trans finSumFinEquiv

theorem blockSum_permutation (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) :
    GeneralLinear.blockSum (GeneralLinear.permutation a R σ, GeneralLinear.permutation b R τ) =
      GeneralLinear.permutation (a + b) R (gaugeBlockPermutation σ τ) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [GeneralLinear.permutation_entry, gaugeBlockPermutation]
  all_goals
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega

theorem reindex_permutation (e : Fin n ≃ Fin m) (σ : Equiv.Perm (Fin n)) :
    GeneralLinear.reindex e (GeneralLinear.permutation n R σ) =
      GeneralLinear.permutation m R ((e.symm.trans σ).trans e) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  simp [GeneralLinear.reindex, GeneralLinear.permutation_entry, Matrix.reindex_apply]
  change (if σ.symm i = j then (1 : R) else 0) =
    if σ j = i then 1 else 0
  by_cases h : σ j = i
  · have h' : σ.symm i = j := σ.symm_apply_eq.mpr h.symm
    simp only [ite_eq_left h', ite_eq_left h]
  · have h' : σ.symm i ≠ j := fun he => h (σ.symm_apply_eq.mp he).symm
    simp only [ite_eq_right h', ite_eq_right h]

theorem permutation_mem_unitary {𝕜 : Type*} [RCLike 𝕜] (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    (GeneralLinear.permutation n 𝕜 σ : Matrix (Fin n) (Fin n) 𝕜) ∈
      Matrix.unitaryGroup (Fin n) 𝕜 := by
  rw [GeneralLinear.permutation_coe, Matrix.mem_unitaryGroup_iff]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix, inv_inv,
    ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

end PermutationMatrices

variable (F : Type u) [Field F] [NumberField F]

/-- Every adelic permutation matrix belongs to the standard compact subgroup. -/
theorem permutation_mem_standardCompact (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    GeneralLinear.permutation n (Adeles F) σ ∈ PrimitiveAdelicHeight.standardCompact F n := by
  rw [PrimitiveAdelicHeight.mem_standardCompact_iff, mem_standardInfiniteCompact_iff,
    FiniteAdelicGL.mem_standardIntegral]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro v
    have he : ArchimedeanGL.realMatrix F n (archimedeanGLCoordinates F n
        (AdelicGL.infinite F n (GeneralLinear.permutation n (Adeles F) σ))) v =
        (GeneralLinear.permutation n ℝ σ : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      simp only [ArchimedeanGL.realMatrix, archimedeanGLCoordinates_apply,
        AdelicGL.infinite_apply, GeneralLinear.permutation_entry]
      split_ifs
      · exact map_one (InfinitePlace.Completion.extensionEmbeddingOfIsReal v.property)
      · exact map_zero (InfinitePlace.Completion.extensionEmbeddingOfIsReal v.property)
    rw [he]
    exact permutation_mem_unitary n σ
  · intro v
    have he : ArchimedeanGL.complexMatrix F n (archimedeanGLCoordinates F n
        (AdelicGL.infinite F n (GeneralLinear.permutation n (Adeles F) σ))) v =
        (GeneralLinear.permutation n ℂ σ : Matrix (Fin n) (Fin n) ℂ) := by
      ext i j
      simp only [ArchimedeanGL.complexMatrix, archimedeanGLCoordinates_apply,
        AdelicGL.infinite_apply, GeneralLinear.permutation_entry]
      split_ifs
      · exact map_one (InfinitePlace.Completion.extensionEmbedding v.val)
      · exact map_zero (InfinitePlace.Completion.extensionEmbedding v.val)
    rw [he]
    exact permutation_mem_unitary n σ
  · intro i j v
    simp only [AdelicGL.finite_apply, GeneralLinear.permutation_entry]
    split_ifs
    · exact (v.adicCompletionIntegers F).one_mem
    · exact (v.adicCompletionIntegers F).zero_mem
  · intro i j v
    rw [← map_inv, GeneralLinear.permutation_inv, AdelicGL.finite_apply,
      GeneralLinear.permutation_entry]
    split_ifs
    · exact (v.adicCompletionIntegers F).one_mem
    · exact (v.adicCompletionIntegers F).zero_mem

/-- The permutation fixing the first block and reversing the complementary block. -/
def unfoldingWeylPermutation {r t : ℕ} (h : t < r) : Equiv.Perm (Fin (r + 1)) :=
  let e := finCongr (Nat.add_sub_of_le (Nat.le_of_lt (Nat.succ_lt_succ h)))
  (e.symm.trans (gaugeBlockPermutation (Equiv.refl (Fin (t + 1))) Fin.revPerm)).trans e

theorem unfoldingWeyl_eq_permutation {r t : ℕ} (h : t < r) :
    GeneralLinearGroupPoints.adelicEquiv F (r + 1) (unfoldingWeyl F h) =
      GeneralLinear.permutation (r + 1) (Adeles F) (unfoldingWeylPermutation h) := by
  simp only [unfoldingWeyl, MulEquiv.apply_symm_apply, GeneralLinear.weylLong]
  rw [show (1 : Langlands.GeneralLinear (t + 1) (Adeles F)) =
    GeneralLinear.permutation (t + 1) (Adeles F) (Equiv.refl _) from
      (map_one _).symm]
  rw [blockSum_permutation, reindex_permutation]
  rfl

/-- The actual adelic unfolding Weyl representative belongs to the standard compact. -/
theorem unfoldingWeyl_mem_standardCompact {r t : ℕ} (h : t < r) :
    GeneralLinearGroupPoints.adelicEquiv F (r + 1) (unfoldingWeyl F h) ∈
      PrimitiveAdelicHeight.standardCompact F (r + 1) := by
  rw [unfoldingWeyl_eq_permutation]
  exact permutation_mem_standardCompact F (r + 1) _

end Langlands.Global.RankinSelbergGlobal
