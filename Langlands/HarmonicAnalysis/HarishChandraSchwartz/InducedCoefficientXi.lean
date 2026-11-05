import Langlands.Representation.Plancherel.CompactProductCoefficientBounds
import Langlands.Representation.Plancherel.CompactCoefficientHaarComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientBound

/-! # Induced coefficients are bounded by `Ξ` (Waldspurger, Lemma VI.2.2)

Waldspurger, Lemma VI.2.2 (printed pp. 298–299): coefficients of the induced representation
`I_P^G(ω)` are bounded by `C Ξ(g)`. The proof writes the coefficient as an integral over `K`,
bounds the integrand by `C δ_P(m_P(k g))^{1/2} Ξ^M(m_P(k g))` using Corollary III.1.2 for `M`,
and applies Lemma II.1.6.

This module applies `LeviData.norm_compactIntegral_le_xi` to the coefficient map
`CompactInduction.coefficientMap` of the product-induced representation: its value at `g` is
the integral over `K` of `CompactInduction.integrand`, and `integrand_bound_levi` bounds the
integrand through the Iwasawa factorization `k g = q k₁`.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel
open scoped NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G)
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (hK : IsCompact (K : Set G))

/-- The integrand of the coefficient map, written as a function `Φ(k, x)` evaluated at
`x = k g`: `Φ(k, x) = integrand(k⁻¹ x)(k)`. -/
def inducedIntegrandKernel (F : productInducedCoefficientObject h hU A) (k : K) (x : G) : ℂ :=
  CompactInduction.integrand h hU A K ((k : G)⁻¹ * x) F k

omit [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
theorem inducedIntegrandKernel_mul (F : productInducedCoefficientObject h hU A) (k : K)
    (g : G) :
    inducedIntegrandKernel h hU A K F k ((k : G) * g) =
      CompactInduction.integrand h hU A K g F k := by
  unfold inducedIntegrandKernel
  rw [inv_mul_cancel_left]

variable {P₀ : Subgroup G} {δ₀ : P₀ →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ}
  [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)]

include hK in
omit [T2Space G] [CompactSpace (K : Subgroup G)] in
/-- **The integrand bound** in the form of `LeviData.norm_compactIntegral_le_xi`: with
`δ_P = closedRestrictCharacter` and `m_P = h.projection`, and Corollary III.1.2 for `M` as the
hypothesis `hcoeff` (with `Ξ^M = xi hMK δ₀M`), there is `C > 0` with
`|Φ(k, x)| ≤ C δ_P(m_P(x))^{1/2} Ξ^M(m_P(x))` for all `k ∈ K`, `x ∈ G`. -/
theorem norm_inducedIntegrandKernel_le (hδ : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * xi hMK δ₀M m)
    (F : productInducedCoefficientObject h hU A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : K) (x : G), ‖inducedIntegrandKernel h hU A K F k x‖ ≤
      C * leviXiWeight (hP₀K.mono hL.le_P₀) h.projection
        (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) hMK δ₀M x := by
  obtain ⟨C, hC, hb⟩ := CompactInduction.integrand_bound_levi h hU A K hδ hK
    (xi hMK δ₀M) (fun m => integral_nonneg fun k => iwasawaWeight_nonneg _) hcoeff F
  refine ⟨C, hC, fun k x => ?_⟩
  obtain ⟨k₁, hk₁, hx⟩ := exists_iwasawaFactor (hP₀K.mono hL.le_P₀) x
  have he : (k : G) * ((k : G)⁻¹ * x) = (iwasawaFactor (hP₀K.mono hL.le_P₀) x : G) *
      ((⟨k₁, hk₁⟩ : K) : G) := by
    rw [mul_inv_cancel_left]
    exact hx
  refine (hb _ k ⟨k₁, hk₁⟩ _ he).trans (le_of_eq ?_)
  unfold leviXiWeight leviComponent
  ring

/-- **Lemma VI.2.2 for the product-induced coefficient map**: if Corollary III.1.2 holds for
`M` with `Ξ^M` (hypothesis `hcoeff`), then every coefficient `g ↦ coefficientMap F g` of the
normalized induced representation is bounded by `C Ξ(g)`. -/
theorem norm_coefficientMap_le_xi [LocallyCompactSpace P] (hP : IsClosed (P : Set G))
    (hm : Continuous h.projection) (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
    (hG : ∀ g : G, Measure.modularCharacter g = 1)
    (hδP : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
    (hA : A.IsAdmissible) (hδ : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * xi hMK δ₀M m)
    (F : productInducedCoefficientObject h hU A) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : G,
      ‖CompactInduction.coefficientMap h hU A K hK hP hm hPK hG hδP hA F g‖ ≤
        C * xi hP₀K δ₀ g := by
  obtain ⟨C, hC, hb⟩ := norm_inducedIntegrandKernel_le h hU A K hK hδ hL hP₀K hMK hcoeff F
  refine ⟨C, hC, fun g => ?_⟩
  have hint : CompactInduction.coefficientMap h hU A K hK hP hm hPK hG hδP hA F g =
      compactIntegral (K : Subgroup G) (inducedIntegrandKernel h hU A K F) g := by
    rw [CompactInduction.coefficientMap_integral, CompactInduction.measure_eq_normalizedHaar K hK]
    unfold compactIntegral
    simp_rw [inducedIntegrandKernel_mul]
    rfl
  rw [hint]
  exact hL.norm_compactIntegral_le_xi K.isOpen hP₀K hMK hδ₀ hb g

end Langlands.HarishChandraSchwartz
