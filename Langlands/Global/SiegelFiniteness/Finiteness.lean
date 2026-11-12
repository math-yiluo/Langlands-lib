import Langlands.Global.SiegelFiniteness.Heights
import Langlands.Automorphic.CuspidalAdmissible.SiegelGeometry
import Langlands.Global.SiegelFiniteness.Comparison
import Langlands.Global.SiegelFiniteness.CompactBlock

/-!
# Siegel finiteness for the adelic `GL_n` Siegel sets

If `γ h = h'` with `h, h'` in a Siegel set, write `h = N · diag(ω) · A_x · κ` and
`h' = N' · diag(ω') · A_{x'} · κ'`. Then `γ = N' · M · N⁻¹` with
`M = diag(ω') A_{x'} m A_x⁻¹ diag(ω)⁻¹` and `m = κ' κ⁻¹` in the standard compact subgroup. The
entry `M_{ab}` is `e^{x'_a - x_b} · ω'_a m_{ab} ω_b⁻¹` (the exponential acting at the infinite
places). The key inequality makes `x` and `x'` comparable; for `a, b` the difference
`x'_a - x_b` is bounded unless `x` has a large drop at some `s` with `a < s ≤ b`, and then `γ`
and hence `m` vanish in the lower-left block at `s`, so by unitarity the archimedean component
of `m_{ab}` vanishes. Hence all entries of `γ` (and of `γ⁻¹`) lie in one compact set of adeles,
and only finitely many rational matrices do.
-/

noncomputable section

universe u

open scoped NNReal Matrix Pointwise
open NumberField

set_option autoImplicit false

namespace Langlands.Global.SiegelFiniteness

open PrimitiveAdelicHeight Automorphic.CuspidalL2

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The entries of the middle factor. -/
theorem middle_apply (ω ω' : Fin n → Ideles F) (x x' : Fin n → ℝ) (m : AdelicGL F n)
    (a b : Fin n) :
    ((diagonalGL ω' * AdelicGL.ofInfinite F n (torInf F n x') * m *
        (AdelicGL.ofInfinite F n (torInf F n x))⁻¹ * (diagonalGL ω)⁻¹ : AdelicGL F n) :
        Matrix (Fin n) (Fin n) (Adeles F)) a b =
      realScale F (Real.exp (x' a - x b)) *
        ((ω' a).val * (m : Matrix (Fin n) (Fin n) (Adeles F)) a b * ((ω b)⁻¹ : Ideles F).val) := by
  rw [ofInfinite_torInf_inv]
  have hW : ((diagonalGL ω' : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) =
      Matrix.diagonal fun i => (ω' i).val := rfl
  have hWi : (((diagonalGL ω)⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) =
      Matrix.diagonal fun i => ((ω i)⁻¹ : Ideles F).val := rfl
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, hW, hWi,
    ofInfinite_torInf_val, ofInfinite_torInf_val, Matrix.mul_diagonal, Matrix.mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul]
  have hexp : realScale F (Real.exp (x' a - x b)) =
      realScale F (Real.exp (x' a)) * realScale F (Real.exp ((-x) b)) := by
    rw [← realScale_mul, ← Real.exp_add, Pi.neg_apply, sub_eq_add_neg]
  rw [hexp]
  ring

/-- The compact set containing the entries of the middle factor. -/
def middleSet (C : Set (Ideles F)) (Λ : ℝ) : Set (Adeles F) :=
  (fun p : ℝ × Adeles F => realScale F p.1 * p.2) ''
    (Set.Icc 0 (Real.exp Λ) ×ˢ ⋃ a : Fin n, ⋃ b : Fin n,
      (fun p : Ideles F × AdelicGL F n × Ideles F =>
        p.1.val * (p.2.1 : Matrix (Fin n) (Fin n) (Adeles F)) a b * (p.2.2⁻¹ : Ideles F).val) ''
        (C ×ˢ (standardCompact F n : Set (AdelicGL F n)) ×ˢ C))

theorem isCompact_middleSet {C : Set (Ideles F)} (hC : IsCompact C) (Λ : ℝ) :
    IsCompact (middleSet F n C Λ) := by
  refine (isCompact_Icc.prod (isCompact_iUnion fun a => isCompact_iUnion fun b =>
    (hC.prod ((isCompact_standardCompact F n).prod hC)).image ?_)).image
    (((continuous_realScale F).comp continuous_fst).mul continuous_snd)
  exact ((Units.continuous_val.comp continuous_fst).mul
    ((Units.continuous_val.matrix_elem a b).comp (continuous_fst.comp continuous_snd))).mul
    (Units.continuous_coe_inv.comp (continuous_snd.comp continuous_snd))

/-- The compact set containing all entries of the rational matrices in question. -/
def entrySet (ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))) (C : Set (Ideles F)) (Λ : ℝ) :
    Set (Adeles F) :=
  ⋃ i : Fin n, ⋃ j : Fin n,
    (fun p : Matrix (Fin n) (Fin n) (Adeles F) × Matrix (Fin n) (Fin n) (Adeles F) ×
        Matrix (Fin n) (Fin n) (Adeles F) => (p.1 * p.2.1 * p.2.2.adjugate) i j) ''
      (ΩN ×ˢ (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => middleSet F n C Λ) ×ˢ ΩN)

theorem isCompact_entrySet {ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))} (hΩ : IsCompact ΩN)
    {C : Set (Ideles F)} (hC : IsCompact C) (Λ : ℝ) : IsCompact (entrySet F n ΩN C Λ) := by
  refine isCompact_iUnion fun i => isCompact_iUnion fun j => ?_
  refine (hΩ.prod ((isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_middleSet F n hC Λ).prod hΩ)).image ?_
  exact ((continuous_fst.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul
    (continuous_snd.comp continuous_snd).matrix_adjugate).matrix_elem i j

variable {F n}

theorem isUpperTriangular_diagonalGL (ω : Fin n → Ideles F) :
    ((diagonalGL ω : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)).IsUpperTriangular :=
  Matrix.blockTriangular_diagonal _

theorem isUpperTriangular_diagonalGL_inv (ω : Fin n → Ideles F) :
    (((diagonalGL ω)⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)).IsUpperTriangular :=
  Matrix.blockTriangular_diagonal _

theorem isUpperTriangular_torus (x : Fin n → ℝ) :
    ((AdelicGL.ofInfinite F n (torInf F n x) : AdelicGL F n) :
      Matrix (Fin n) (Fin n) (Adeles F)).IsUpperTriangular := by
  rw [ofInfinite_torInf_val]
  exact Matrix.blockTriangular_diagonal _

theorem isUpperTriangular_inv {g : AdelicGL F n}
    (hg : (g : Matrix (Fin n) (Fin n) (Adeles F)).IsUpperTriangular) :
    ((g⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)).IsUpperTriangular := by
  have : Invertible (g : Matrix (Fin n) (Fin n) (Adeles F)) := Units.invertible g
  have h := Matrix.blockTriangular_inv_of_blockTriangular hg
  rwa [← Matrix.coe_units_inv] at h

theorem inv_val_eq_adjugate {g : AdelicGL F n}
    (hg : PrimitiveAdelicHeight.IsUnitriangular (g : Matrix (Fin n) (Fin n) (Adeles F))) :
    ((g⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) =
      (g : Matrix (Fin n) (Fin n) (Adeles F)).adjugate := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, hg.det_eq_one, Ring.inverse_one, one_smul]

/-- **The compact part is block upper triangular wherever `γ` is.** -/
theorem isBlockUpper_compactPart {Ngl Ngl' : AdelicGL F n} {ω ω' : Fin n → Ideles F}
    {x x' : Fin n → ℝ} {κ κ' : AdelicGL F n} {γ : AdelicGL F n}
    (hN : (Ngl : Matrix (Fin n) (Fin n) (Adeles F)).IsUpperTriangular)
    (hN' : (Ngl' : Matrix (Fin n) (Fin n) (Adeles F)).IsUpperTriangular)
    (hγ : γ * (Ngl * diagonalGL ω * AdelicGL.ofInfinite F n (torInf F n x) * κ) =
      Ngl' * diagonalGL ω' * AdelicGL.ofInfinite F n (torInf F n x') * κ')
    {s : ℕ} (hγs : IsBlockUpper s (γ : Matrix (Fin n) (Fin n) (Adeles F))) :
    IsBlockUpper s ((κ' * κ⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) := by
  have hκ' : κ' = (Ngl' * diagonalGL ω' * AdelicGL.ofInfinite F n (torInf F n x'))⁻¹ *
      (γ * (Ngl * diagonalGL ω * AdelicGL.ofInfinite F n (torInf F n x) * κ)) := by
    rw [hγ]
    group
  have hm : κ' * κ⁻¹ = (AdelicGL.ofInfinite F n (torInf F n x'))⁻¹ * (diagonalGL ω')⁻¹ *
      Ngl'⁻¹ * γ * (Ngl * diagonalGL ω * AdelicGL.ofInfinite F n (torInf F n x)) := by
    rw [hκ']
    group
  rw [hm]
  simp only [Units.val_mul]
  have u := fun {M : Matrix (Fin n) (Fin n) (Adeles F)} (h : M.IsUpperTriangular) =>
    isBlockUpper_of_isUpperTriangular h s
  exact ((((u (isUpperTriangular_inv (isUpperTriangular_torus x'))).mul
    (u (isUpperTriangular_diagonalGL_inv ω'))).mul (u (isUpperTriangular_inv hN'))).mul hγs).mul
    (u ((hN.mul (isUpperTriangular_diagonalGL ω)).mul (isUpperTriangular_torus x)))

end Langlands.Global.SiegelFiniteness
