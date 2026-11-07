import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedFourierTransform
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermBound

/-! # Normalized induction preserves temperedness (Waldspurger, Lemma III.2.3)

Waldspurger, Lemma III.2.3 (printed p. 266): if `P = M U` is a semi-standard parabolic subgroup
of `G` and `(π, V)` is an admissible tempered representation of `M`, then `(I_P^G π, I_P^G V)` is
tempered. Waldspurger proves this through the exponent criterion of Proposition III.2.2 and the
computation of the Jacquet modules of `I_P^G π` in I.3.

This module proves it by the analytic route of the proofs of Corollary III.1.2 and Lemma VI.2.2:
a coefficient of `I_P^G π` is the integral over `K` of `δ_P(m_P(k g))^{1/2}` times a coefficient
of `π` at `m_P(k g)`; temperedness of `π` bounds the latter by `c Ξ^M(m) (1 + σ_M(m))^R`, a bound
`σ_M(m_P(q)) ≤ c (1 + σ(q k))` for the Levi component (`LeviSigmaBound`) replaces `σ_M` by `σ`,
and Lemma II.1.6 (`LeviData.xi_eq_integral`) turns the remaining integral into `Ξ(g)`.

* `LeviSigmaBound`: the bound on `σ_M` of Levi components, with
  `leviSigmaBound_of_sigmaProductBound` deriving it for `σ_M = σ|_M` from Lemma II.3.1
  (`SigmaProductBound M U σ`) and the right `K`-invariance of `σ`;
* `LeviData.norm_compactIntegral_le_xi_mul_rpow`: the analytic core, for an integral over `K`
  of a function `Φ(k, k g)` bounded by `C δ_P(m_P(x))^{1/2} Ξ^M(m_P(x)) (1 + σ(x))^r`, with `σ`
  left `K`-invariant;
* `exists_coefficientTensorMap_le_rpow`: one tempered bound for finitely many coefficient
  tensors of a tempered representation;
* `norm_inducedIntegrandKernel_le_rpow`: the integrand bound;
* `hasTemperedCoefficients_normalizedInduction_of_tempered`: Lemma III.2.3;
* `hasTemperedCoefficients_normalizedInduction_of_sigmaProductBound`: Lemma III.2.3 for
  `σ_M = σ|_M`, with Lemma II.3.1 and the bi-`K`-invariance of `σ` as hypotheses.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel
open scoped NNReal TensorProduct

namespace Langlands.HarishChandraSchwartz

universe u uG uV

section LeviSigma

variable {G : Type uG} [Group G] {P M U : Subgroup G}

/-- The bound `σ_M(m_P(q)) ≤ c (1 + σ(q k))` for all `q ∈ P` and `k ∈ K`, for functions `σ` on
`G` and `σ_M` on the Levi subgroup `M`, where `m_P : P → M` is the Levi projection. For
Waldspurger's `σ` and `σ_M = σ|_M` it follows from Lemma II.3.1 and the right `K`-invariance of
`σ` (`leviSigmaBound_of_sigmaProductBound`). -/
def LeviSigmaBound (h : IsSemidirectDecomposition P M U) (K : Set G) (σ : G → ℝ) (σM : M → ℝ) :
    Prop :=
  ∃ c : ℝ, ∀ q : P, ∀ k ∈ K, σM (h.projection q) ≤ c * (1 + σ ((q : G) * k))

/-- `LeviSigmaBound` for `σ_M = σ|_M` from the second inequality of Lemma II.3.1
(`SigmaProductBound M U σ`) and the right `K`-invariance of `σ`: writing `q = m u` with
`m = m_P(q)`, `C (1 + σ(m)) ≤ 1 + σ(m u) = 1 + σ(q k)`. -/
theorem leviSigmaBound_of_sigmaProductBound (h : IsSemidirectDecomposition P M U) {K : Set G}
    {σ : G → ℝ} (hσU : SigmaProductBound M U σ) (hσK : ∀ g, ∀ k ∈ K, σ (g * k) = σ g) :
    LeviSigmaBound h K σ (fun m => σ m) := by
  obtain ⟨C, hC, hb⟩ := hσU
  refine ⟨C⁻¹, fun q k hk => ?_⟩
  have h1 := hb (h.projection q) ⟨_, h.projection_inv_mul_mem q⟩
  rw [mul_inv_cancel_left] at h1
  rw [hσK _ k hk]
  have h2 : C * (1 + σ (h.projection q)) ≤ 1 + σ q :=
    (mul_le_mul_of_nonneg_left (by gcongr; exact le_max_left _ _) hC.le).trans h1
  have h3 : 1 + σ (h.projection q) ≤ C⁻¹ * (1 + σ q) := by
    rw [inv_mul_eq_div, le_div_iff₀ hC]
    linarith
  linarith

end LeviSigma

section Core

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable {K P₀ P M : Subgroup G} [CompactSpace K] [CompactSpace (K.subgroupOf M)]
variable {δ₀ : P₀ →* ℝ≥0ˣ} {δP : M →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ} {mP : P →* M}

/-- **The analytic core with a polynomial weight**: if
`|Φ(k, x)| ≤ C δ_P(m_P(x))^{1/2} Ξ^M(m_P(x)) (1 + σ(x))^r` for all `k ∈ K` and `x ∈ G`, and `σ`
is invariant under left translation by `K`, then `|∫_K Φ(k, k g) dk| ≤ C Ξ(g) (1 + σ(g))^r`. -/
theorem LeviData.norm_compactIntegral_le_xi_mul_rpow [SecondCountableTopology G]
    (hL : LeviData K P₀ P M δ₀ δP δ₀M mP) (hK : IsOpen (K : Set G))
    (hP₀K : IsIwasawaPair P₀ K) (hM : IsIwasawaPair (P₀.subgroupOf M) (K.subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1) {σ : G → ℝ}
    (hσK : ∀ k ∈ K, ∀ g, σ (k * g) = σ g) {Φ : K → G → ℂ} {C r : ℝ}
    (hΦ : ∀ (k : K) (x : G), ‖Φ k x‖ ≤
      C * leviXiWeight (hP₀K.mono hL.le_P₀) mP δP hM δ₀M x * (1 + σ x) ^ r)
    (g : G) :
    ‖compactIntegral K Φ g‖ ≤ C * xi hP₀K δ₀ g * (1 + σ g) ^ r := by
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
      ≤ ∫ k : K, C * (1 + σ g) ^ r *
          leviXiWeight (hP₀K.mono hL.le_P₀) mP δP hM δ₀M ((k : G) * g) ∂(normalizedHaar K) :=
        norm_integral_le_of_norm_le (hint.const_mul _)
          (Filter.Eventually.of_forall fun k => (hΦ k _).trans_eq (by rw [hσK k k.2]; ring))
    _ = C * xi hP₀K δ₀ g * (1 + σ g) ^ r := by
        rw [integral_const_mul, hxi]
        unfold leviXiWeight
        ring

end Core

section TensorBounds

variable {L : Type uG} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  (A : SmoothRep.{0, uG, uV} ℂ L) {ξ σL : L → ℝ}

/-- A single tempered bound `|c_t(m)| ≤ C ξ(m) (1 + σ_L(m))^R` with `C, R ≥ 0` for the
coefficient function of one coefficient tensor of a representation with tempered
coefficients. -/
theorem exists_coefficientTensorMap_le_rpow_of_tensor (hξ : ∀ m, 0 ≤ ξ m)
    (hσL : ∀ m, 0 ≤ σL m) (hT : HasTemperedCoefficients ξ σL A.representation)
    (t : CoefficientTensor A) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧
      ∀ m, ‖coefficientTensorMap A t m‖ ≤ C * (ξ m * (1 + σL m) ^ R) := by
  have hone : ∀ m, 1 ≤ 1 + σL m := fun m => le_add_of_nonneg_right (hσL m)
  have hmono : ∀ {R R' : ℝ} (m : L), R ≤ R' →
      ξ m * (1 + σL m) ^ R ≤ ξ m * (1 + σL m) ^ R' := fun m hR =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hone m) hR) (hξ m)
  have hw : ∀ (R : ℝ) (m : L), 0 ≤ ξ m * (1 + σL m) ^ R := fun R m =>
    mul_nonneg (hξ m) (Real.rpow_nonneg (zero_le_one.trans (hone m)) _)
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    obtain ⟨c, r, hc⟩ := hT v ℓ
    refine ⟨max c 0, max r 0, le_max_right _ _, le_max_right _ _, fun m => ?_⟩
    rw [coefficientTensorMap_tmul]
    calc ‖ℓ.val (A.representation m v)‖ ≤ c * ξ m * (1 + σL m) ^ r := hc m
      _ = c * (ξ m * (1 + σL m) ^ r) := mul_assoc _ _ _
      _ ≤ max c 0 * (ξ m * (1 + σL m) ^ r) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (hw r m)
      _ ≤ max c 0 * (ξ m * (1 + σL m) ^ max r 0) :=
          mul_le_mul_of_nonneg_left (hmono m (le_max_left _ _)) (le_max_right _ _)
  | add t s ht hs =>
    obtain ⟨C₁, R₁, hC₁, hR₁, h₁⟩ := ht
    obtain ⟨C₂, R₂, hC₂, hR₂, h₂⟩ := hs
    refine ⟨C₁ + C₂, max R₁ R₂, add_nonneg hC₁ hC₂, le_max_of_le_left hR₁, fun m => ?_⟩
    calc ‖coefficientTensorMap A (t + s) m‖
        ≤ ‖coefficientTensorMap A t m‖ + ‖coefficientTensorMap A s m‖ := by
          rw [map_add, LocallyConstant.add_apply]
          exact norm_add_le _ _
      _ ≤ C₁ * (ξ m * (1 + σL m) ^ max R₁ R₂) + C₂ * (ξ m * (1 + σL m) ^ max R₁ R₂) :=
          add_le_add ((h₁ m).trans (mul_le_mul_of_nonneg_left
              (hmono m (le_max_left _ _)) hC₁))
            ((h₂ m).trans (mul_le_mul_of_nonneg_left (hmono m (le_max_right _ _)) hC₂))
      _ = (C₁ + C₂) * (ξ m * (1 + σL m) ^ max R₁ R₂) := (add_mul _ _ _).symm

/-- One tempered bound `|c_t(m)| ≤ C ξ(m) (1 + σ_L(m))^R`, with `C > 0` and `R ≥ 0`, for all
the tensors `t` of a finite set, for a representation with tempered coefficients. -/
theorem exists_coefficientTensorMap_le_rpow (hξ : ∀ m, 0 ≤ ξ m) (hσL : ∀ m, 0 ≤ σL m)
    (hT : HasTemperedCoefficients ξ σL A.representation) (S : Set (CoefficientTensor A))
    (hS : S.Finite) :
    ∃ C R : ℝ, 0 < C ∧ 0 ≤ R ∧ ∀ t ∈ S, ∀ m,
      ‖coefficientTensorMap A t m‖ ≤ C * (ξ m * (1 + σL m) ^ R) := by
  choose c R hc hR hb using exists_coefficientTensorMap_le_rpow_of_tensor A hξ hσL hT
  obtain ⟨B, hB⟩ := (hS.image c).bddAbove
  obtain ⟨D, hD⟩ := (hS.image R).bddAbove
  refine ⟨max 1 B, max 0 D, lt_max_of_lt_left zero_lt_one, le_max_left _ _, ?_⟩
  intro t ht m
  have hone : 1 ≤ 1 + σL m := le_add_of_nonneg_right (hσL m)
  calc ‖coefficientTensorMap A t m‖ ≤ c t * (ξ m * (1 + σL m) ^ R t) := hb t m
    _ ≤ max 1 B * (ξ m * (1 + σL m) ^ max 0 D) :=
        mul_le_mul ((hB ⟨t, ht, rfl⟩).trans (le_max_right 1 B))
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hone
            ((hD ⟨t, ht, rfl⟩).trans (le_max_right 0 D))) (hξ m))
          (mul_nonneg (hξ m) (Real.rpow_nonneg (zero_le_one.trans hone) _))
          (zero_le_one.trans (le_max_left 1 B))

end TensorBounds

section Induced

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  {P₀ : Subgroup G} {δ₀ : P₀ →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ}
  [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)]

include hK in
omit [T2Space G] [CompactSpace (K : Subgroup G)] in
/-- **The integrand bound for a tempered `M`-representation**: if the coefficients of `A` have
tempered growth for `Ξ^M` and `σ_M ≥ 0`, and the Levi components satisfy
`σ_M(m_P(q)) ≤ c (1 + σ(q k))` for `q ∈ P`, `k ∈ K`, with `σ ≥ 0`, then there are `C > 0`,
`R ≥ 0` with `|Φ(k, x)| ≤ C δ_P(m_P(x))^{1/2} Ξ^M(m_P(x)) (1 + σ(x))^R`. -/
theorem norm_inducedIntegrandKernel_le_rpow (hδ : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    {σ : G → ℝ} {σM : M → ℝ} (hσ : ∀ g, 0 ≤ σ g) (hσM : ∀ m, 0 ≤ σM m)
    (hlevi : LeviSigmaBound h (K : Set G) σ σM)
    (hT : HasTemperedCoefficients (xi hMK δ₀M) σM A.representation)
    (F : productInducedCoefficientObject h hU A) :
    ∃ C R : ℝ, 0 < C ∧ 0 ≤ R ∧ ∀ (k : K) (x : G), ‖inducedIntegrandKernel h hU A K F k x‖ ≤
      C * leviXiWeight (hP₀K.mono hL.le_P₀) h.projection
        (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) hMK δ₀M x *
          (1 + σ x) ^ R := by
  have hξ : ∀ m, 0 ≤ xi hMK δ₀M m := fun m => integral_nonneg fun k => iwasawaWeight_nonneg _
  obtain ⟨C₀, R, hC₀, hR, hb⟩ := exists_coefficientTensorMap_le_rpow A hξ hσM hT
    (Set.range (CompactInduction.compactValue h hU A K F))
    (CompactInduction.compactValue_range_finite h hU A K hK F)
  obtain ⟨c, hc⟩ := hlevi
  set c' := max c 0 with hc'
  have hc'0 : 0 ≤ c' := le_max_right _ _
  refine ⟨C₀ * (1 + c') ^ R, R, mul_pos hC₀ (Real.rpow_pos_of_pos (by linarith) _), hR,
    fun k x => ?_⟩
  obtain ⟨k₁, hk₁, hx⟩ := exists_iwasawaFactor (hP₀K.mono hL.le_P₀) x
  set q := iwasawaFactor (hP₀K.mono hL.le_P₀) x with hq
  have he : (k : G) * ((k : G)⁻¹ * x) = (q : G) * ((⟨k₁, hk₁⟩ : K) : G) := by
    rw [mul_inv_cancel_left]
    exact hx
  have hfac := CompactInduction.integrand_factorization h hU A K F _ k ⟨k₁, hk₁⟩ q he
  have hn : ‖(HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂ)‖ =
      (NNReal.sqrt
        (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
          (h.projection q) : ℝ≥0) : ℝ) := by
    rw [closedHalfCharacter_eq_comp_projection h hU hδ, MonoidHom.comp_apply]
    change ‖(((NNReal.sqrt
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
        (h.projection q) : ℝ≥0) : ℝ) : ℂ))‖ = _
    rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  have hσq : 1 + σM (h.projection q) ≤ (1 + c') * (1 + σ x) := by
    have h1 : σM (h.projection q) ≤ c' * (1 + σ x) := by
      have := hc q k₁ hk₁
      rw [← hx] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith [hσ x]))
    nlinarith [hσ x]
  have hpow : (1 + σM (h.projection q)) ^ R ≤ (1 + c') ^ R * (1 + σ x) ^ R := by
    rw [← Real.mul_rpow (by linarith) (by linarith [hσ x])]
    exact Real.rpow_le_rpow (by linarith [hσM (h.projection q)]) hσq hR
  have hsq : 0 ≤ (NNReal.sqrt (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
      (h.projection q) : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  unfold inducedIntegrandKernel
  rw [hfac, norm_mul, hn]
  unfold leviXiWeight leviComponent
  rw [← hq]
  calc (NNReal.sqrt (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
          (h.projection q) : ℝ≥0) : ℝ) *
        ‖coefficientTensorMap A (CompactInduction.compactValue h hU A K F (⟨k₁, hk₁⟩, k))
          (h.projection q)‖
      ≤ (NNReal.sqrt (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
          (h.projection q) : ℝ≥0) : ℝ) *
        (C₀ * (xi hMK δ₀M (h.projection q) * (1 + σM (h.projection q)) ^ R)) :=
        mul_le_mul_of_nonneg_left (hb _ ⟨_, rfl⟩ _) hsq
    _ ≤ (NNReal.sqrt (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
          (h.projection q) : ℝ≥0) : ℝ) *
        (C₀ * (xi hMK δ₀M (h.projection q) * ((1 + c') ^ R * (1 + σ x) ^ R))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (hξ _)) hC₀.le) hsq
    _ = _ := by ring

include hK in
/-- **Lemma III.2.3** (Waldspurger, printed p. 266): if the coefficients of the admissible
representation `A` of `M` have tempered growth for `Ξ^M` and `σ_M`, then the coefficients of the
normalized induced representation `I_P^G A` have tempered growth for `Ξ` and `σ`. The hypotheses
on `σ`, `σ_M` are nonnegativity, left `K`-invariance of `σ` and the bound
`σ_M(m_P(q)) ≤ c (1 + σ(q k))` (`q ∈ P`, `k ∈ K`) for the Levi components. -/
theorem hasTemperedCoefficients_normalizedInduction_of_tempered [LocallyCompactSpace P]
    (hP : IsClosed (P : Set G))
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
    {σ : G → ℝ} {σM : M → ℝ} (hσ : ∀ g, 0 ≤ σ g) (hσM : ∀ m, 0 ≤ σM m)
    (hσK : ∀ k ∈ K, ∀ g, σ (k * g) = σ g) (hlevi : LeviSigmaBound h (K : Set G) σ σM)
    (hT : HasTemperedCoefficients (xi hMK δ₀M) σM A.representation) :
    HasTemperedCoefficients (xi hP₀K δ₀) σ
      ((normalizedInductionFunctor h hU).obj A).representation := by
  intro v ℓ
  let E := CompactInduction.coefficientTensorEquiv h hU A K hK hP hm hPK hG hδP hA
  obtain ⟨C, R, -, -, hb⟩ := norm_inducedIntegrandKernel_le_rpow h hU A K hK hδ hL hP₀K hMK
    hσ hσM hlevi hT (E.symm (v ⊗ₜ[ℂ] ℓ))
  refine ⟨C, R, fun g => ?_⟩
  have he : CompactInduction.coefficientMap h hU A K hK hP hm hPK hG hδP hA
      (E.symm (v ⊗ₜ[ℂ] ℓ)) g = ℓ.val (((normalizedInductionFunctor h hU).obj A).representation
        g v) := by
    change coefficientTensorMap _ (E (E.symm (v ⊗ₜ[ℂ] ℓ))) g = _
    rw [Representation.Equiv.apply_symm_apply, coefficientTensorMap_tmul]
  have hint : CompactInduction.coefficientMap h hU A K hK hP hm hPK hG hδP hA
      (E.symm (v ⊗ₜ[ℂ] ℓ)) g =
      compactIntegral (K : Subgroup G) (inducedIntegrandKernel h hU A K (E.symm (v ⊗ₜ[ℂ] ℓ))) g := by
    rw [CompactInduction.coefficientMap_integral, CompactInduction.measure_eq_normalizedHaar K hK]
    unfold compactIntegral
    simp_rw [inducedIntegrandKernel_mul]
    rfl
  beta_reduce
  rw [← he, hint]
  exact hL.norm_compactIntegral_le_xi_mul_rpow K.isOpen hP₀K hMK hδ₀ hσK hb g

include hK in
/-- **Lemma III.2.3 for `σ_M = σ|_M`** (Waldspurger, printed p. 266): if `σ ≥ 0` is
bi-invariant under `K` and satisfies the second inequality of Lemma II.3.1 for `P = M U`
(`SigmaProductBound M U σ`), and the coefficients of the admissible representation `A` of `M`
have tempered growth for `Ξ^M` and the restriction of `σ` to `M`, then the coefficients of
`I_P^G A` have tempered growth for `Ξ` and `σ`. -/
theorem hasTemperedCoefficients_normalizedInduction_of_sigmaProductBound [LocallyCompactSpace P]
    (hP : IsClosed (P : Set G))
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
    {σ : G → ℝ} (hσ : ∀ g, 0 ≤ σ g) (hσK : ∀ k ∈ K, ∀ g, σ (k * g) = σ g)
    (hσK' : ∀ g, ∀ k ∈ K, σ (g * k) = σ g) (hσU : SigmaProductBound M U σ)
    (hT : HasTemperedCoefficients (xi hMK δ₀M) (fun m : M => σ m) A.representation) :
    HasTemperedCoefficients (xi hP₀K δ₀) σ
      ((normalizedInductionFunctor h hU).obj A).representation :=
  hasTemperedCoefficients_normalizedInduction_of_tempered h hU A K hK hP hm hPK hG hδP hA hδ hL
    hP₀K hMK hδ₀ hσ (fun m => hσ m) hσK (leviSigmaBound_of_sigmaProductBound h hσU hσK') hT

end Induced

end Langlands.HarishChandraSchwartz
