import Langlands.HarmonicAnalysis.Distribution.RenardHaarStatements
import Langlands.Representation.Hecke.CommonInvarianceProof

/-! # Inversion and positive scalar consequences of left Haar uniqueness -/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution.RenardHaar

open Langlands.Hecke
open GroupAction

universe uG

section Inversion

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem isPositive_inversion {T : Distribution G} (hT : IsPositive T) :
    IsPositive (inversionDistributions T) := by
  intro f hf hpos
  apply hT (inversionTests f)
  · intro hz
    apply hf
    simpa using congrArg inversionTests hz
  · intro x
    exact hpos x⁻¹

theorem isRightInvariant_inversion {T : Distribution G} (hT : IsLeftInvariant T) :
    IsRightInvariant (inversionDistributions T) := by
  intro g
  rw [← inversionDistributions_leftDistributions, hT g]

theorem isLeftInvariant_inversion {T : Distribution G} (hT : IsRightInvariant T) :
    IsLeftInvariant (inversionDistributions T) := by
  intro g
  rw [← inversionDistributions_rightDistributions, hT g]

end Inversion

/-- Unweighted inversion transports the full-dual left Haar assertion to the
right Haar assertion, preserving strict positivity and the same scalar. -/
theorem rightHaar_of_leftHaar (hleft : LeftHaarStatement.{uG}) :
    RightHaarStatement.{uG} := by
  intro G _ _ _ _ _ _
  obtain ⟨T, hTpos, hTinv, hTunique⟩ := hleft G
  refine ⟨inversionDistributions T, isPositive_inversion hTpos,
    isRightInvariant_inversion hTinv, ?_⟩
  intro S hSinv
  obtain ⟨c, hc, hcu⟩ :=
    hTunique (inversionDistributions S) (isLeftInvariant_inversion hSinv)
  refine ⟨c, ?_, ?_⟩
  · simpa using congrArg inversionDistributions hc
  · intro d hd
    apply hcu d
    simpa using congrArg inversionDistributions hd

section PositiveScalars

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

theorem exists_nonzero_nonnegative_test :
    ∃ f : SchwartzBruhat G, f ≠ 0 ∧ IsNonnegativeTest f := by
  classical
  obtain ⟨K, _, hK, _⟩ :=
    TestFunction.commonCompactOpenBiInvariance G ∅ ⊤
  refine ⟨TestFunction.subgroupIndicator K hK, ?_, ?_⟩
  · intro hz
    have hv := congrArg (fun f : SchwartzBruhat G => f 1) hz
    simp at hv
  · intro x
    by_cases hx : x ∈ K <;> simp [TestFunction.subgroupIndicator_apply, hx]

theorem ne_zero_of_isPositive {T : Distribution G} (hT : IsPositive T) : T ≠ 0 := by
  obtain ⟨f, hf, hpos⟩ := exists_nonzero_nonnegative_test (G := G)
  intro hz
  have ht := (hT f hf hpos).2
  simp [hz] at ht

/-- A complex scalar taking one strictly positive distribution to another
has zero imaginary part and strictly positive real part. -/
theorem scalar_positive_of_isPositive {T S : Distribution G}
    (hT : IsPositive T) (hS : IsPositive S) {c : ℂ} (hc : S = c • T) :
    c.im = 0 ∧ 0 < c.re := by
  obtain ⟨f, hf, hpos⟩ := exists_nonzero_nonnegative_test (G := G)
  have ht := hT f hf hpos
  have hs := hS f hf hpos
  have he : S f = c * T f := congrArg (fun D : Distribution G => D f) hc
  have him : c.im * (T f).re = 0 := by
    have h := congrArg Complex.im he
    simpa [Complex.mul_im, ht.1, hs.1] using h.symm
  have hci : c.im = 0 := (mul_eq_zero.mp him).resolve_right (ne_of_gt ht.2)
  have hre : (S f).re = c.re * (T f).re := by
    simpa [Complex.mul_re, ht.1] using congrArg Complex.re he
  exact ⟨hci, (mul_pos_iff_of_pos_right ht.2).mp (hre ▸ hs.2)⟩

omit [Group G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] in
private theorem complex_multiple_of_common_generator
    {T S H : Distribution G} (hT : T ≠ 0)
    (hTH : ∃ a : ℂ, T = a • H) (hSH : ∃ b : ℂ, S = b • H) :
    ∃ c : ℂ, S = c • T := by
  obtain ⟨a, ha⟩ := hTH
  obtain ⟨b, hb⟩ := hSH
  have hane : a ≠ 0 := by
    intro hz
    apply hT
    simpa [hz] using ha
  refine ⟨b / a, ?_⟩
  rw [ha, smul_smul, div_mul_cancel₀ _ hane, ← hb]

theorem positive_real_multiple {T S : Distribution G}
    (hT : IsPositive T) (hS : IsPositive S) (hmul : ∃ c : ℂ, S = c • T) :
    ∃! c : ℝ, 0 < c ∧ S = (c : ℂ) • T := by
  obtain ⟨c, hc⟩ := hmul
  obtain ⟨hci, hcr⟩ := scalar_positive_of_isPositive hT hS hc
  have hcreal : (c.re : ℂ) = c := by
    apply Complex.ext <;> simp [hci]
  have hval : S = (c.re : ℂ) • T := by
    rw [hcreal]
    exact hc
  refine ⟨c.re, ⟨hcr, hval⟩, ?_⟩
  intro d hd
  have he : (d : ℂ) = (c.re : ℂ) :=
    smul_left_injective ℂ (ne_zero_of_isPositive hT) (hd.2.symm.trans hval)
  exact_mod_cast he

end PositiveScalars

/-- Full-dual left Haar uniqueness implies the positive-real uniqueness
assertion for distributions invariant on either common side. -/
theorem positiveScalarUniqueness_of_leftHaar (hleft : LeftHaarStatement.{uG}) :
    PositiveScalarUniquenessStatement.{uG} := by
  intro G _ _ _ _ _ _ T S hT hS hinv
  apply positive_real_multiple hT hS
  rcases hinv with hleftInv | hrightInv
  · obtain ⟨H, _, _, hH⟩ := hleft G
    exact complex_multiple_of_common_generator (ne_zero_of_isPositive hT)
      (ExistsUnique.exists (hH T hleftInv.1))
      (ExistsUnique.exists (hH S hleftInv.2))
  · obtain ⟨H, _, _, hH⟩ := rightHaar_of_leftHaar hleft G
    exact complex_multiple_of_common_generator (ne_zero_of_isPositive hT)
      (ExistsUnique.exists (hH T hrightInv.1))
      (ExistsUnique.exists (hH S hrightInv.2))

end Langlands.HarmonicAnalysis.Distribution.RenardHaar
