import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalInverse

/-! # Comparison of spherical functions for compact open subgroups -/

noncomputable section

open MeasureTheory Measure TopologicalSpace
open scoped NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe u

section Weights

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {P K L : Subgroup G} [CompactSpace L]
  {hPK : IsIwasawaPair P K} {hPL : IsIwasawaPair P L} {δ : P →* ℝ≥0ˣ}

/-- Positive Iwasawa weights for two compact factorizations are uniformly comparable. -/
theorem exists_pos_iwasawaWeight_le_mul
    (hδK : ∀ p : P, (p : G) ∈ K → δ p = 1)
    (hδL : ∀ p : P, (p : G) ∈ L → δ p = 1)
    (hKo : IsOpen (K : Set G)) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : G, iwasawaWeight hPK δ g ≤ C * iwasawaWeight hPL δ g := by
  have hLc : IsCompact (L : Set G) := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨C, hC⟩ := hLc.bddAbove_image (continuous_iwasawaWeight hδK hKo).continuousOn
  have hC1 : 1 ≤ C := by
    have h := hC ⟨1, L.one_mem, rfl⟩
    rwa [iwasawaWeight_of_mem (hPK := hPK) hδK K.one_mem] at h
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC1, fun g => ?_⟩
  obtain ⟨p, hp, l, hl, rfl⟩ := hPL g
  rw [iwasawaWeight_mul_left hδK ⟨p, hp⟩,
    iwasawaWeight_mul hδL hp hl]
  have h := mul_le_mul_of_nonneg_left (hC ⟨l, hl, rfl⟩)
    (show 0 ≤ (NNReal.sqrt (δ ⟨p, hp⟩ : ℝ≥0) : ℝ) from NNReal.coe_nonneg _)
  simpa only [mul_comm] using h

end Weights

section Averages

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {P K L : Subgroup G} [LocallyCompactSpace P] [CompactSpace K] [CompactSpace L]
  {hPK : IsIwasawaPair P K} {hPL : IsIwasawaPair P L} {δ : P →* ℝ≥0ˣ}

include hPK in
/-- The compact-average invariance theorem for real-valued covariant functions. -/
theorem integral_compact_mul_right
    (hG : ∀ g : G, modularCharacter g = 1) (hP : IsClosed (P : Set G))
    (hKo : IsOpen (K : Set G)) (φ : G → ℝ) (hφ : Continuous φ)
    (hcov : ∀ (p : P) (x : G), φ ((p : G) * x) =
      (modularCharacter p : ℝ) * φ x) (g : G) :
    (∫ k : K, φ ((k : G) * g) ∂normalizedHaar K) =
      ∫ k : K, φ k ∂normalizedHaar K := by
  have h := compactAverage_mul_right hG hP hKo hPK (fun x => (φ x : ℂ))
    (Complex.continuous_ofReal.comp hφ) (fun p x => by
      rw [hcov, Complex.ofReal_mul]) g
  unfold compactAverage at h
  simp only [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

include hPK in
/-- Changing the compact subgroup multiplies the covariant integral by one scalar. -/
theorem integral_compact_eq_mul
    (hG : ∀ g : G, modularCharacter g = 1) (hP : IsClosed (P : Set G))
    (hKo : IsOpen (K : Set G))
    (hδ : ∀ p : P, (δ p : ℝ≥0) = modularCharacter p)
    (hδL : ∀ p : P, (p : G) ∈ L → δ p = 1)
    (φ : G → ℝ) (hφ : Continuous φ)
    (hcov : ∀ (p : P) (x : G), φ ((p : G) * x) = (δ p : ℝ≥0) * φ x) :
    (∫ k : K, φ k ∂normalizedHaar K) =
      (∫ k : K, iwasawaWeight hPL δ (k : G) ^ 2 ∂normalizedHaar K) *
        ∫ l : L, φ l ∂normalizedHaar L := by
  have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology L := TopologicalSpace.Subtype.secondCountableTopology _
  let F : K → L → ℝ := fun k l => φ ((k : G) * l)
  have hFc : Continuous (Function.uncurry F) :=
    hφ.comp ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))
  have hFi : Integrable (Function.uncurry F) ((normalizedHaar K).prod (normalizedHaar L)) :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hinnerK (l : L) : (∫ k : K, F k l ∂normalizedHaar K) =
      ∫ k : K, φ k ∂normalizedHaar K :=
    integral_compact_mul_right (hPK := hPK) hG hP hKo φ hφ
      (fun p x => by rw [← hδ p]; exact hcov p x) l
  have hinnerL (k : K) : (∫ l : L, F k l ∂normalizedHaar L) =
      iwasawaWeight hPL δ (k : G) ^ 2 * ∫ l : L, φ l ∂normalizedHaar L := by
    obtain ⟨p, hp, l₀, hl₀, he⟩ := hPL k
    have hpt (l : L) : F k l = (δ ⟨p, hp⟩ : ℝ≥0) * φ ((l₀ : G) * l) := by
      change φ ((k : G) * l) = _
      rw [he, mul_assoc]
      exact hcov ⟨p, hp⟩ _
    have hsq : iwasawaWeight hPL δ (k : G) ^ 2 = (δ ⟨p, hp⟩ : ℝ≥0) := by
      rw [he, iwasawaWeight_mul hδL hp hl₀]
      exact_mod_cast NNReal.sq_sqrt (δ ⟨p, hp⟩ : ℝ≥0)
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hsq]
    congr 1
    have h := integral_mul_left_eq_self (μ := normalizedHaar L)
      (fun l : L => φ l) ⟨l₀, hl₀⟩
    exact h
  calc (∫ k : K, φ k ∂normalizedHaar K) =
        ∫ l : L, ∫ k : K, F k l ∂normalizedHaar K ∂normalizedHaar L := by
          simp only [hinnerK, integral_const, measureReal_def, measure_univ,
            ENNReal.toReal_one, one_smul]
    _ = ∫ k : K, ∫ l : L, F k l ∂normalizedHaar L ∂normalizedHaar K :=
      (integral_integral_swap hFi).symm
    _ = _ := by
      simp only [hinnerL]
      exact integral_mul_const _ _

end Averages

section Spherical

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {P K L : Subgroup G} [LocallyCompactSpace P] [CompactSpace K] [CompactSpace L]
  {hPK : IsIwasawaPair P K} {hPL : IsIwasawaPair P L} {δ : P →* ℝ≥0ˣ}

/-- Spherical functions constructed with two compact open subgroups are uniformly comparable. -/
theorem exists_xi_le_mul_xi
    (hG : ∀ g : G, modularCharacter g = 1) (hP : IsClosed (P : Set G))
    (hKo : IsOpen (K : Set G)) (hLo : IsOpen (L : Set G))
    (hδ : ∀ p : P, (δ p : ℝ≥0) = modularCharacter p) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : G, xi hPK δ g ≤ C * xi hPL δ g := by
  have hδK := modular_eq_one_of_mem hP hKo hδ
  have hδL := modular_eq_one_of_mem hP hLo hδ
  obtain ⟨c, hc, hcomp⟩ := exists_pos_iwasawaWeight_le_mul
    (hPK := hPK) (hPL := hPL) hδK hδL hKo
  let D := ∫ k : K, iwasawaWeight hPL δ (k : G) ^ 2 ∂normalizedHaar K
  have hbound (g : G) : xi hPK δ g ≤ (c ^ 2 * D) * xi hPL δ g := by
    let φ : G → ℝ := fun x => iwasawaWeight hPL δ (x * g) * iwasawaWeight hPL δ x
    have hw := continuous_iwasawaWeight hδL hLo (hPK := hPL)
    have hφ : Continuous φ := (hw.comp (continuous_id.mul continuous_const)).mul hw
    have hcov (p : P) (x : G) : φ ((p : G) * x) = (δ p : ℝ≥0) * φ x := by
      dsimp [φ]
      rw [mul_assoc, iwasawaWeight_mul_left hδL, iwasawaWeight_mul_left hδL]
      have hs : (NNReal.sqrt (δ p : ℝ≥0) : ℝ) ^ 2 = (δ p : ℝ≥0) := by
        exact_mod_cast NNReal.sq_sqrt (δ p : ℝ≥0)
      calc
        _ = (NNReal.sqrt (δ p : ℝ≥0) : ℝ) ^ 2 *
            (iwasawaWeight hPL δ (x * g) * iwasawaWeight hPL δ x) := by ring
        _ = _ := by rw [hs]
    have hchange := integral_compact_eq_mul (hPK := hPK) (hPL := hPL)
      hG hP hKo hδ hδL φ hφ hcov
    have hL : (∫ l : L, φ l ∂normalizedHaar L) = xi hPL δ g := by
      unfold xi
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun l => by
        dsimp [φ]
        rw [iwasawaWeight_of_mem hδL l.2, mul_one]
    have hpoint (k : K) : iwasawaWeight hPK δ ((k : G) * g) ≤ c ^ 2 * φ k := by
      have ht := mul_le_mul (hcomp ((k : G) * g)) (hcomp k)
        (iwasawaWeight_nonneg (hPK := hPK) (δ := δ) k)
        (mul_nonneg hc.le (iwasawaWeight_nonneg (hPK := hPL) (δ := δ) _))
      rw [iwasawaWeight_of_mem hδK k.2, mul_one] at ht
      dsimp [φ]
      convert ht using 1; ring
    calc xi hPK δ g ≤ ∫ k : K, c ^ 2 * φ k ∂normalizedHaar K :=
        integral_mono (integrable_iwasawaWeight_mul hδK hKo g)
          ((hφ.comp continuous_subtype_val).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _ ) |>.const_mul _) hpoint
      _ = c ^ 2 * (D * xi hPL δ g) := by
        rw [integral_const_mul, hchange, hL]
      _ = _ := by ring
  refine ⟨c ^ 2 * D, ?_, hbound⟩
  have h1 := hbound 1
  rw [xi_one hδK, xi_one hδL, mul_one] at h1
  exact lt_of_lt_of_le zero_lt_one h1

end Spherical

/-- The comparison needed when the structural compact subgroup and the subgroup
defining the spherical function differ. -/
def XiCompactComparisonStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G],
    (∀ g : G, modularCharacter g = 1) →
    ∀ (P : Subgroup G) [LocallyCompactSpace P], IsClosed (P : Set G) →
    ∀ (K L : Subgroup G) [CompactSpace K] [CompactSpace L],
      IsOpen (K : Set G) → IsOpen (L : Set G) →
    ∀ (hPK : IsIwasawaPair P K) (hPL : IsIwasawaPair P L) (δ : P →* ℝ≥0ˣ),
      (∀ p : P, (δ p : ℝ≥0) = modularCharacter p) →
      ∃ C : ℝ, 0 < C ∧ ∀ g : G, xi hPK δ g ≤ C * xi hPL δ g

/-- Uniform comparison of the spherical functions for two compact open subgroups. -/
theorem xiCompactComparison : XiCompactComparisonStatement.{u} := by
  intro G _ _ _ _ _ _ _ hG P _ hP K L _ _ hKo hLo hPK hPL δ hδ
  exact exists_xi_le_mul_xi hG hP hKo hLo hδ

end Langlands.HarishChandraSchwartz
