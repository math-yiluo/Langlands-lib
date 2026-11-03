import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteRationalRestrictionNorm
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeLaurentRetraction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartBaseChange

/-! # Finite rational inverse norm bounds over every complete coefficient field -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K} {I : Type v} [Fintype I]
  (D : I → RationalChart K A)

/-- Transfer a finite rational inverse estimate along an actual isometric coefficient map.
The auxiliary scalar field acts only on the enlarged algebra and its chart quotients. -/
theorem exists_norm_bound_of_isometric_baseMap
    (φ : BoundedAlgHom K A B) (hφ : ∀ a : A, ‖φ a‖ = ‖a‖)
    (L : Type w) [NontriviallyNormedField L] [NormedAlgebra L B]
    (hcover : ∀ x : BanachSpectrum A, ∃ i, x ∈ (D i).locus) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : A, ‖a‖ ≤ C * ‖fun i => (D i).baseMap a‖ := by
  classical
  let E := fun i => pullback φ (D i)
  have hcov : ∀ x : BanachSpectrum B, ∃ i, x ∈ (E i).locus := by
    intro x
    obtain ⟨i, hi⟩ := hcover (BanachSpectrum.comap φ.toBoundedRingHom x)
    refine ⟨i, ?_⟩
    change x ∈ (pullback φ (D i)).locus
    rwa [pullback_locus]
  obtain ⟨C, hCpos, hC⟩ := AuxiliaryScalar.exists_norm_bound E L hcov
  choose M hMpos hM using fun i => (pullbackMap φ (D i)).bounded
  have hsum : 0 ≤ ∑ i, M i := Finset.sum_nonneg fun i _ => (hMpos i).le
  have hMi (i : I) : M i ≤ (∑ j, M j) + 1 := by
    apply (Finset.single_le_sum (fun j _ => (hMpos j).le) (Finset.mem_univ i)).trans
    linarith
  have hprod (a : A) :
      ‖fun i => (E i).baseMap (φ a)‖ ≤
        ((∑ i, M i) + 1) * ‖fun i => (D i).baseMap a‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by linarith) (norm_nonneg _))).2
    intro i
    change ‖(pullback φ (D i)).baseMap (φ a)‖ ≤ _
    rw [← pullbackMap_baseMap]
    exact (hM i _).trans
      (mul_le_mul (hMi i) (norm_le_pi_norm (fun j => (D j).baseMap a) i)
        (norm_nonneg _) (by linarith))
  refine ⟨C * ((∑ i, M i) + 1), mul_pos hCpos (by linarith), fun a => ?_⟩
  calc
    ‖a‖ = ‖φ a‖ := (hφ a).symm
    _ ≤ C * ‖fun i => (E i).baseMap (φ a)‖ := hC (φ a)
    _ ≤ C * (((∑ i, M i) + 1) * ‖fun i => (D i).baseMap a‖) :=
      mul_le_mul_of_nonneg_left (hprod a) hCpos.le
    _ = _ := (mul_assoc _ _ _).symm

/-- Every finite rational cover has a positive inverse norm estimate,
including over trivially valued original fields. -/
theorem exists_finiteRestrictionBound
    (hcover : ∀ x : BanachSpectrum A, ∃ i, x ∈ (D i).locus) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : A, ‖a‖ ≤ C * ‖fun i => (D i).baseMap a‖ := by
  classical
  by_cases hK : ∃ z : K, 1 < ‖z‖
  · let : NontriviallyNormedField K :=
      { (inferInstance : NormedField K) with non_trivial := hK }
    exact AuxiliaryScalar.exists_norm_bound D K hcover
  · have hle (a : K) : ‖a‖ ≤ 1 := le_of_not_gt fun ha => hK ⟨a, ha⟩
    have hnorm (a : K) (ha : a ≠ 0) : ‖a‖ = 1 := by
      apply le_antisymm (hle a)
      have hp : ‖a‖ * ‖a⁻¹‖ = 1 := by
        rw [← norm_mul, mul_inv_cancel₀ ha, norm_one]
      have hh := mul_le_mul_of_nonneg_left (hle a⁻¹) (norm_nonneg a)
      rwa [hp, mul_one] at hh
    have hind : ∀ (a : K) (n : ℤ), n ≠ 0 → ‖a‖ ≠ (2 : ℝ) ^ n := by
      intro a n hn heq
      by_cases ha : a = 0
      · have ht : 0 < (2 : ℝ) ^ n := zpow_pos (by norm_num) _
        rw [ha, norm_zero] at heq
        linarith
      · rw [hnorm a ha] at heq
        exact hn ((zpow_eq_one_iff_right₀ (by norm_num : 0 ≤ (2 : ℝ))
          (by norm_num : (2 : ℝ) ≠ 1)).mp heq.symm)
    let : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
    let : Fact (∀ (a : K) (n : ℤ), n ≠ 0 → ‖a‖ ≠ (2 : ℝ) ^ n) := ⟨hind⟩
    let : NontriviallyNormedField (CompletedGaussLaurent K 2) :=
      { RelativeLaurentAnnulus.ScalarExtension.independentNormedField K 2 with
        non_trivial := ⟨CompletedGaussLaurent.X, by
          rw [CompletedGaussLaurent.norm_X]
          norm_num⟩ }
    exact exists_norm_bound_of_isometric_baseMap D
      (RelativeLaurentAnnulus.baseMap K A 2)
      (RelativeLaurentAnnulus.norm_baseMap K A 2)
      (CompletedGaussLaurent K 2) hcover

/-- A chosen positive inverse norm constant for the actual finite rational restriction. -/
def finiteRestrictionBound
    (hcover : ∀ x : BanachSpectrum A, ∃ i, x ∈ (D i).locus) : ℝ :=
  (exists_finiteRestrictionBound D hcover).choose

theorem finiteRestrictionBound_pos
    (hcover : ∀ x : BanachSpectrum A, ∃ i, x ∈ (D i).locus) :
    0 < finiteRestrictionBound D hcover :=
  (exists_finiteRestrictionBound D hcover).choose_spec.1

theorem norm_le_finiteRestrictionBound
    (hcover : ∀ x : BanachSpectrum A, ∃ i, x ∈ (D i).locus) (a : A) :
    ‖a‖ ≤ finiteRestrictionBound D hcover * ‖finiteRestriction D a‖ :=
  (exists_finiteRestrictionBound D hcover).choose_spec.2 a

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
