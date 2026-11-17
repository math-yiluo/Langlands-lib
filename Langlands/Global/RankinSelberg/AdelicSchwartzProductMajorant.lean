import Langlands.Global.RankinSelberg.AdelicRowMajorant
import Langlands.Global.RankinSelberg.EqualAnalyticDominated

/-! # Product majorants for dominated adelic rows -/

noncomputable section
universe u
open NumberField
open scoped Classical
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace AdelicSchwartzMellin

variable (F : Type u) [Field F] [NumberField F]

/-- A dominated row function of positive length is bounded by a product of
copies of one rank-one Schwartz--Bruhat function. -/
theorem exists_product_schwartzBruhat_majorant {n : ℕ} (hn : 0 < n)
    {Φ : RowVector F n → ℂ} (hΦ : EqualAnalytic.IsRowDominated F n Φ) :
    ∃ Ψ : RowVector F 1 → ℂ, Ψ ∈ schwartzBruhat F 1 ∧
      ∀ x, ‖Φ x‖ ≤ ∏ j : Fin n, ‖Ψ (fun _ _ => x 0 j)‖ := by
  obtain ⟨d, hd, hsupp, hrapid⟩ := hΦ
  let z : RowVector F n × Fin n → RowVector F 1 :=
    fun p _ _ => p.1 0 p.2
  let w : RowVector F n × Fin n → ℝ :=
    fun p => ‖Φ p.1‖ ^ ((n : ℝ)⁻¹)
  have hw : ∀ p, 0 ≤ w p := fun p => Real.rpow_nonneg (norm_nonneg _) _
  have hz : ∀ p, ‖archimedeanCoordinates F 1 (z p)‖ ≤
      ‖archimedeanCoordinates F n p.1‖ := by
    intro p
    change ‖fun _ : Fin 1 => archimedeanCoordinates F n p.1 p.2‖ ≤ _
    rw [pi_norm_const]
    exact norm_le_pi_norm (archimedeanCoordinates F n p.1) p.2
  have hwr : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ p, (1 + ‖archimedeanCoordinates F 1 (z p)‖) ^ N * w p ≤ C := by
    intro N
    obtain ⟨C, hC⟩ := hrapid (N * n)
    refine ⟨(max C 0) ^ ((n : ℝ)⁻¹),
      Real.rpow_nonneg (le_max_right _ _) _, fun p => ?_⟩
    have hb : ((1 + ‖archimedeanCoordinates F 1 (z p)‖) ^ N * w p) ^ n ≤
        max C 0 := by
      rw [mul_pow, show w p ^ n = ‖Φ p.1‖ by
        exact Real.rpow_inv_natCast_pow (norm_nonneg _) hn.ne',
        ← pow_mul]
      exact (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith [hz p]) _)
        (norm_nonneg _)).trans ((hC p.1).trans (le_max_left _ _))
    have hr := Real.rpow_le_rpow (by positivity) hb
      (inv_nonneg.mpr (Nat.cast_nonneg n))
    rwa [Real.pow_rpow_inv_natCast (by positivity) hn.ne'] at hr
  have hdF : (d : F) ≠ 0 := by exact_mod_cast hd
  have hwsupp : ∀ p, w p ≠ 0 →
      finiteCoordinates F 1 (z p) ∈ SchwartzMajorant.denominatorRows F 1 (d : F) := by
    intro p hp i
    have hpΦ : Φ p.1 ≠ 0 := by
      intro h
      apply hp
      simp only [w, h, norm_zero, Real.zero_rpow (by positivity : (n : ℝ)⁻¹ ≠ 0)]
    simpa only [z, finiteCoordinates, ← IsScalarTower.algebraMap_apply (𝓞 F) F
      (FiniteAdeles F)] using hsupp p.1 hpΦ p.2
  obtain ⟨Ψ, hΨ, hbound, -⟩ :=
    SchwartzMajorant.exists_schwartzBruhat_majorant F z w hw hwr (d : F) hdF hwsupp
  refine ⟨Ψ, hΨ, fun x => ?_⟩
  calc
    ‖Φ x‖ = ∏ _j : Fin n, ‖Φ x‖ ^ ((n : ℝ)⁻¹) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact (Real.rpow_inv_natCast_pow (norm_nonneg _) hn.ne').symm
    _ ≤ ∏ j : Fin n, ‖Ψ (fun _ _ => x 0 j)‖ :=
      Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
        (fun j _ => hbound (x, j))

end AdelicSchwartzMellin

end Langlands.Global.RankinSelbergGlobal
