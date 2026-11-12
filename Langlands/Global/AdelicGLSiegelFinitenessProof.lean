import Langlands.Global.SiegelFiniteness.Entries

/-!
# Siegel finiteness for the adelic `GL_n` Siegel sets

Proof of `Langlands.Global.PrimitiveAdelicHeight.SiegelSetGLFinitenessStatement`: for every
Siegel set `𝔖`, only finitely many rational `γ` satisfy `γ 𝔖 ∩ 𝔖 ≠ ∅`.
-/

noncomputable section

universe u

open scoped NNReal Matrix

set_option autoImplicit false

namespace Langlands.Global.PrimitiveAdelicHeight

/-- **Siegel finiteness.** -/
theorem siegelSetGLFiniteness : SiegelSetGLFinitenessStatement.{u} := by
  intro F _ _ n ΩN C c hΩ hΩN hC _ hc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · apply Set.Subsingleton.finite
    intro γ₁ _ γ₂ _
    apply Units.ext
    funext i
    exact i.elim0
  obtain ⟨Q₁, K, hQ₁, hK, hdata⟩ := exists_siegel_data F n ΩN C c hΩ hΩN hC hc
  obtain ⟨β₀, hkey₀⟩ := SiegelFiniteness.exists_key_bound F n hn hQ₁
  have hβ : 0 ≤ max β₀ 0 := le_max_right _ _
  have hkey : ∀ (x x' : Fin n → ℝ) (q q' : AdelicGL F n), q ∈ Q₁ → q' ∈ Q₁ →
      ∀ γ : RationalGL F n,
        AdelicGL.rational F n γ * (AdelicGL.ofInfinite F n (torInf F n x) * q) =
          AdelicGL.ofInfinite F n (torInf F n x') * q' →
        ∀ t j : Fin n, (γ⁻¹ : RationalGL F n).val t j ≠ 0 → x' j ≤ x t + max β₀ 0 :=
    fun x x' q q' hq hq' γ hγ t j htj =>
      (hkey₀ x x' q q' hq hq' γ hγ t j htj).trans (by linarith [le_max_left β₀ 0])
  set Λ : ℝ := (max β₀ 0 + 2 * n * K) + n * K +
    n * ((max β₀ 0 + 2 * n * K) + max β₀ 0 + 2 * n * K) with hΛ
  have hE := SiegelFiniteness.isCompact_entrySet F n hΩ hC Λ
  have hmem : ∀ (γ : RationalGL F n) (h h' : AdelicGL F n), h ∈ siegelSetGL F n ΩN C c →
      h' ∈ siegelSetGL F n ΩN C c → AdelicGL.rational F n γ * h = h' →
      ∀ i j, ((AdelicGL.rational F n γ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) i j ∈
        SiegelFiniteness.entrySet F n ΩN C Λ := by
    intro γ h h' hh hh' hγ i j
    obtain ⟨Ngl, ω, x, κ, hN, hω, hκ, hx, rfl, hq⟩ := hdata h hh
    obtain ⟨Ngl', ω', x', κ', hN', hω', hκ', hx', rfl, hq'⟩ := hdata h' hh'
    exact SiegelFiniteness.entries_mem hΩN hK hβ hkey γ hN hN' hω hω' hκ hκ' hx hx' hq hq' hγ i j
  refine (finite_rational_compact F n {1}
    (AdelicMatrixHeight.entryBox F n (SiegelFiniteness.entrySet F n ΩN C Λ))
    isCompact_singleton (AdelicMatrixHeight.isCompact_entryBox F n hE)).subset ?_
  rintro γ ⟨g, hg, hγg⟩
  refine ⟨1, rfl, ?_⟩
  rw [mul_one]
  refine ⟨fun i j => hmem γ g _ hg hγg rfl i j, fun i j => ?_⟩
  rw [← map_inv]
  exact hmem γ⁻¹ _ g hγg hg (by rw [map_inv, inv_mul_cancel_left]) i j

end Langlands.Global.PrimitiveAdelicHeight
