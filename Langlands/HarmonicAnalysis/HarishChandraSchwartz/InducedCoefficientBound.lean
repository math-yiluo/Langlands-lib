import Langlands.HarmonicAnalysis.HarishChandraSchwartz.LeviWeightIntegrability

/-! # Coefficients of induced representations are bounded by `Ξ` (Waldspurger, Lemma VI.2.2)

Waldspurger, Lemma VI.2.2 (printed pp. 298–299): for `ψ ∈ C^∞(O, P)` there is `C > 0` with
`|(E_P^G ψ_ω)(g)| ≤ C Ξ(g)` for all `ω ∈ O` and `g ∈ G`. The proof writes the coefficient as
`∫_K χ δ_P^{1/2}(m_P(kg)) ⟨ω(m_P(kg)) v(k_P(kg)), v̌(k)⟩ dk`, bounds the inner coefficient by
`C Ξ^M(m_P(kg))` (Corollary III.1.2), and applies Lemma II.1.6.

This module proves the analytic core for abstract data: an integral over `K` of a function
`Φ(k, k g)` with `|Φ(k, x)| ≤ C δ_P(m_P(x))^{1/2} Ξ^M(m_P(x))` is bounded by `C Ξ(g)`. The
representation of the coefficient as such an integral and the bound on `Φ` are hypotheses.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.HarishChandraSchwartz

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable {K P₀ P M : Subgroup G} [CompactSpace K] [CompactSpace (K.subgroupOf M)]
variable {δ₀ : P₀ →* ℝ≥0ˣ} {δP : M →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ} {mP : P →* M}

variable (K) in
/-- The integral `g ↦ ∫_K Φ(k, k g) dk` over `K` with its Haar measure of total mass one: the
form `⟨I_P^G(ω ⊗ χ)(g) v, v̌⟩ = ∫_K ⟨v_χ(k g), v̌(k)⟩ dk` of an induced coefficient in the
proof of Lemma VI.2.2, with `Φ(k, x) = ⟨v_χ(x), v̌(k)⟩`. -/
def compactIntegral (Φ : K → G → ℂ) (g : G) : ℂ :=
  ∫ k : K, Φ k ((k : G) * g) ∂(normalizedHaar K)

/-- **Lemma VI.2.2, analytic core**: if `|Φ(k, x)| ≤ C δ_P(m_P(x))^{1/2} Ξ^M(m_P(x))` for all
`k ∈ K` and `x ∈ G` (`leviXiWeight`), then `|∫_K Φ(k, k g) dk| ≤ C Ξ(g)` for every `g`. -/
theorem LeviData.norm_compactIntegral_le_xi [SecondCountableTopology G]
    (hL : LeviData K P₀ P M δ₀ δP δ₀M mP) (hK : IsOpen (K : Set G))
    (hP₀K : IsIwasawaPair P₀ K) (hM : IsIwasawaPair (P₀.subgroupOf M) (K.subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1) {Φ : K → G → ℂ} {C : ℝ}
    (hΦ : ∀ (k : K) (x : G), ‖Φ k x‖ ≤ C * leviXiWeight (hP₀K.mono hL.le_P₀) mP δP hM δ₀M x)
    (g : G) :
    ‖compactIntegral K Φ g‖ ≤ C * xi hP₀K δ₀ g := by
  unfold compactIntegral
  have hxi := hL.xi_eq_integral hK hP₀K hM hδ₀ g
  have hint : Integrable (fun k : K =>
      leviXiWeight (hP₀K.mono hL.le_P₀) mP δP hM δ₀M ((k : G) * g)) (normalizedHaar K) := by
    apply Integrable.of_integral_ne_zero
    change (∫ k : K, NNReal.sqrt (δP (leviComponent (hP₀K.mono hL.le_P₀) mP ((k : G) * g)) :
        ℝ≥0) * xi hM δ₀M (leviComponent (hP₀K.mono hL.le_P₀) mP ((k : G) * g))
          ∂(normalizedHaar K)) ≠ 0
    rw [← hxi]
    exact (xi_pos hδ₀ hK g).ne'
  calc ‖∫ k : K, Φ k ((k : G) * g) ∂(normalizedHaar K)‖
      ≤ ∫ k : K, C * leviXiWeight (hP₀K.mono hL.le_P₀) mP δP hM δ₀M ((k : G) * g)
          ∂(normalizedHaar K) :=
        norm_integral_le_of_norm_le (hint.const_mul C)
          (Filter.Eventually.of_forall fun k => hΦ k _)
    _ = C * xi hP₀K δ₀ g := by
        rw [integral_const_mul, hxi]
        rfl

/-- The bound is uniform: for a family `Φ_i` satisfying the hypothesis with one constant `C`
(in the application, the twists `ω ⊗ χ` with `χ ∈ Im X(M)`), `|∫_K Φ_i(k, k g) dk| ≤ C Ξ(g)` for
all `i` and `g`. -/
theorem LeviData.norm_compactIntegral_le_xi_uniform [SecondCountableTopology G]
    (hL : LeviData K P₀ P M δ₀ δP δ₀M mP) (hK : IsOpen (K : Set G))
    (hP₀K : IsIwasawaPair P₀ K) (hM : IsIwasawaPair (P₀.subgroupOf M) (K.subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1) {ι : Type*} {Φ : ι → K → G → ℂ} {C : ℝ}
    (hΦ : ∀ (i : ι) (k : K) (x : G),
      ‖Φ i k x‖ ≤ C * leviXiWeight (hP₀K.mono hL.le_P₀) mP δP hM δ₀M x) (i : ι) (g : G) :
    ‖compactIntegral K (Φ i) g‖ ≤ C * xi hP₀K δ₀ g :=
  hL.norm_compactIntegral_le_xi hK hP₀K hM hδ₀ (hΦ i) g

end Langlands.HarishChandraSchwartz
