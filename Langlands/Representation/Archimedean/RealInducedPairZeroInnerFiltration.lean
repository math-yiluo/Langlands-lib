import Langlands.Representation.Archimedean.RealInducedPairDistantParity

/-! # Filtration at the zero inner-weight boundary -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairZeroInnerFiltration

open RealStandardFiltration RealBlockFrobeniusMap RealBlockMultiplier
open RealCharacterPair RealCharacterPairReducible
open RealInducedPairAscendingExchange RealInducedPairLinkedReplacement

variable {d e : ComplexCharacterData} {k : ℕ} {sd se : Fin 2}

/-- A zero exponent difference is generic on either endpoint parity class. -/
theorem exists_zero (c c' : RealCharacterData) :
    ∃ μ : ℤ → ℂ, IsRecurrent 1 (pairParity c c') μ ∧
      IsSymmetric (pairParity c c') (sigma0 c c') μ ∧
      ∀ j, Even (j - pairParity c c') → μ j ≠ 0 := by
  have hε := pairParity_eq c c'
  have hnonneg : 0 ≤ pairParity c c' := by omega
  have hg : IsGenericParameter 0 (pairParity c c') := by
    apply isGenericParameter_of_re_nonneg (by simp) hnonneg
    intro m hm
    have hh := congrArg Complex.re hm
    simp only [Complex.zero_re, Complex.add_re, Complex.intCast_re, Complex.mul_re,
      Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.re_ofNat,
      Complex.im_ofNat, mul_zero, sub_zero] at hh
    have he : (0 : ℝ) ≤ (pairParity c c' : ℝ) := by exact_mod_cast hnonneg
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  obtain ⟨μ, hr, hs, hn⟩ := hg.exists_generic hε
  exact ⟨μ, by simpa only [zero_add] using hr, hs, hn⟩

/-- Only the first crossing is singular at the zero inner-weight boundary. -/
theorem exists_ascendingData (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - 1 - pairParity (P.lo d sd) (P.hi e se)))
    (hH : innerWeight d e k = 0) :
    ∃ μ₀ μ₂ μ₃ : ℤ → ℂ,
      MultiplierData e d se sd
        (binomialMultiplier (outerWeight d e k) (pairParity (P.lo d sd) (P.hi e se)))
        μ₀ μ₂ μ₃ ∧
      (∀ j, Even (j - pairParity (P.lo d sd) (P.lo e se)) → μ₀ j ≠ 0) ∧
      (∀ j, Even (j - pairParity (P.hi d sd) (P.hi e se)) → μ₂ j ≠ 0) ∧
      (∀ j, Even (j - pairParity (P.hi d sd) (P.lo e se)) → μ₃ j ≠ 0) := by
  have hs := RealInducedPairLinkedIncoming.weight_sum d e k
  have hp0 : Even ((d.weight.natAbs : ℤ) -
      pairParity (P.lo d sd) (P.lo e se)) := by
    simp only [pairParity, RealInducedPairQuotientPresentation.lo,
      RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData] at hp ⊢
    rw [Int.even_iff] at hp ⊢
    omega
  have hp2 : Even ((e.weight.natAbs : ℤ) -
      pairParity (P.hi d sd) (P.hi e se)) := by
    simp only [pairParity, RealInducedPairQuotientPresentation.lo,
      RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData] at hp ⊢
    rw [Int.even_iff] at hp ⊢
    omega
  obtain ⟨μ₀, hr0, hs0, hn0⟩ :=
    RealInducedPairDistantParity.exists_middle (P.lo d sd) (P.lo e se) hp0
  obtain ⟨μ₂, hr2, hs2, hn2⟩ :=
    RealInducedPairDistantParity.exists_middle (P.hi d sd) (P.hi e se) hp2
  obtain ⟨μ₃, hr3, hs3, hn3⟩ := exists_zero (P.hi d sd) (P.lo e se)
  obtain ⟨hν1, hν0, hν2, hν3⟩ :=
    RealInducedPairDistantParity.differences (sd := sd) (se := se) h
  refine ⟨μ₀, μ₂, μ₃, ⟨?_, hs0, hs2, hs3, ?_, ?_, ?_, ?_⟩, hn0, hn2, hn3⟩
  · exact isSymmetric_binomialMultiplier _ (pairParity_eq _ _)
  · rw [hν1]
    exact isRecurrent_binomialMultiplier (RealInducedPairOuterTail.outerWeight_pos d e k)
      (pairParity_eq _ _) hp
  · rw [hν0, hH]
    simpa only [Int.cast_zero, zero_add, Int.cast_natCast] using hr0
  · rw [hν2, hH]
    simpa only [Int.cast_zero, zero_add, Int.cast_natCast] using hr2
  · rw [hν3, hH]
    simpa only [Int.cast_zero, zero_add] using hr3

section Word

variable {μ₀ μ₂ μ₃ : ℤ → ℂ}
  (hm : MultiplierData e d se sd
    (binomialMultiplier (outerWeight d e k) (pairParity (P.lo d sd) (P.hi e se)))
    μ₀ μ₂ μ₃)

/-- The three generic crossings following the outer binomial. -/
def suffix : KF 4 (X1 e d se sd) →ₗ[ℂ] KF 4 (P.X d e sd se) :=
  (blockFrobMap hm.data3).comp (RealInducedPairDistantParity.middle hm)

theorem suffix_exact :
    IsRealIntertwinerModulo 4 (X1 e d se sd) (P.X d e sd se) ⊥ (suffix hm) :=
  modulo_comp_bot
    (swap_exact (n := 4) (pre := [.character (P.lo d sd)])
      (post := [.character (P.hi e se)]) rfl hm.sym3 hm.rec3)
    (RealInducedPairDistantParity.middle_exact hm)

theorem suffix_surjective
    (hn0 : ∀ j, Even (j - pairParity (P.lo d sd) (P.lo e se)) → μ₀ j ≠ 0)
    (hn2 : ∀ j, Even (j - pairParity (P.hi d sd) (P.hi e se)) → μ₂ j ≠ 0)
    (hn3 : ∀ j, Even (j - pairParity (P.hi d sd) (P.lo e se)) → μ₃ j ≠ 0) :
    Function.Surjective (suffix hm) := by
  have hlast : Function.Surjective (blockFrobMap hm.data3) := by
    intro f
    let I := blockFrobMap (data_unswap (n := 4) (pre := [.character (P.lo d sd)])
      (post := [.character (P.hi e se)]) rfl hm.sym3)
    exact ⟨I f, RealCharacterInducedPushforward.frob_inv_of_ne_zero hm.data3 _ hn3 f⟩
  exact hlast.comp (RealInducedPairDistantParity.middle_surjective hm hn0 hn2)

theorem first_eq :
    blockFrobMap hm.data1 = RealInducedPairDistantParity.outerBinomial d e k sd se := rfl

theorem crossings_eq : hm.crossings =
    (suffix hm).comp (RealInducedPairDistantParity.outerBinomial d e k sd se) := by
  unfold MultiplierData.crossings
  rw [first_eq hm]
  exact (congrArg (fun F => (blockFrobMap hm.data3).comp F)
    (LinearMap.comp_assoc (RealInducedPairDistantParity.outerBinomial d e k sd se)
      (blockFrobMap hm.data0) (blockFrobMap hm.data20)).symm).trans
    (LinearMap.comp_assoc (RealInducedPairDistantParity.outerBinomial d e k sd se)
      (RealInducedPairDistantParity.middle hm) (blockFrobMap hm.data3)).symm

theorem beforeDescent_eq (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) :
    hm.beforeDescent he hd = ((P.quotientMap d e sd se hd he).comp (suffix hm)).comp
      (RealInducedPairDistantParity.outerBinomial d e k sd se) := by
  unfold MultiplierData.beforeDescent
  rw [crossings_eq hm]
  exact (LinearMap.comp_assoc (RealInducedPairDistantParity.outerBinomial d e k sd se)
    (suffix hm) (P.quotientMap d e sd se hd he)).symm

end Word

/-- The exchanged pair and the outer fused source span the actual target. -/
theorem filtration_of_pieces
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - 1 - pairParity (P.lo d sd) (P.hi e se)))
    (hH : innerWeight d e k = 0)
    {C : List RealBlock → Prop} (hW : C [.induced e, .induced d])
    (hR : C (RealInducedPairDistantParity.outerPiece d e k sd se)) :
    HasFiltration 4 [.induced d, .induced e] C := by
  obtain ⟨μ₀, μ₂, μ₃, hm, hn0, hn2, hn3⟩ := exists_ascendingData h hp hH
  let A := (P.quotientMap d e sd se hd he).comp (suffix hm)
  have hA : IsRealIntertwinerModulo 4 (X1 e d se sd) [.induced d, .induced e] ⊥ A :=
    modulo_comp_bot (RealInducedPairQuotientPresentation.quotient_exact d e sd se hd he)
      (suffix_exact hm)
  have hAs : Function.Surjective A :=
    (RealInducedPairQuotientPresentation.quotient_surjective d e sd se hd he).comp
      (suffix_surjective hm hn0 hn2 hn3)
  obtain ⟨hq, hfac, hrange⟩ := hm.swap_descend he hd
  have hfac' := hfac.trans (beforeDescent_eq hm hd he)
  have hrange' := hrange.trans (congrArg LinearMap.range (beforeDescent_eq hm hd he))
  let qR := A.comp (RealInducedPairDistantParity.outerSection h hp)
  have hqR : IsRealIntertwinerModulo 4
      (RealInducedPairDistantParity.outerPiece d e k sd se) [.induced d, .induced e]
      (LinearMap.range (hm.swap he hd)) qR := by
    rw [hrange']
    exact RealInducedPairDistantFiltration.modulo_comp_range hA
      (RealInducedPairDistantParity.outer_decomposition h hp).1
  apply RealCharacterInducedPushforward.hasFiltration_two hW hR (hm.swap he hd) qR hq hqR
  intro v
  obtain ⟨f, rfl⟩ := hAs v
  obtain ⟨z, r, hf⟩ := (RealInducedPairDistantParity.outer_decomposition h hp).2 f
  refine ⟨P.quotientMap e d se sd he hd z, r, ?_⟩
  change (hm.swap he hd) (P.quotientMap e d se sd he hd z) +
    A (RealInducedPairDistantParity.outerSection h hp r) = A f
  have hz : (hm.swap he hd) (P.quotientMap e d se sd he hd z) =
      A (RealInducedPairDistantParity.outerBinomial d e k sd se z) :=
    LinearMap.congr_fun hfac' z
  rw [hz, ← map_add, hf]

/-- Positive original weights make the outer fused source heavier at the boundary. -/
theorem filtration (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : innerWeight d e k = 0) :
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e) := by
  have hs := RealInducedPairLinkedIncoming.weight_sum d e k
  have hP : outerWeight d e k = d.weight.natAbs + e.weight.natAbs := by omega
  have hb : d.weight.natAbs ^ 2 + e.weight.natAbs ^ 2 < outerWeight d e k ^ 2 := by
    rw [hP]
    nlinarith
  apply (realAdjacentFiltration_iff 4 [] [] (.induced d) (.induced e)).mpr
  apply filtration_of_pieces (sd := 0)
    (se := RealInducedPairDistantParity.selectedParity d e k) hd he h
    (RealInducedPairDistantParity.selectedParity_outer d e k) hH
  · exact ⟨[.induced e, .induced d], rfl, Or.inl rfl⟩
  · refine ⟨RealInducedPairDistantParity.outerPiece d e k 0
      (RealInducedPairDistantParity.selectedParity d e k), rfl,
      Or.inr ⟨RealInducedPairDistantParity.outer_support h, ?_⟩⟩
    rw [RealInducedPairDistantParity.outer_weightSquareSum]
    simpa [realWeightSquareSum, realBlockWeightSquare] using hb

end RealInducedPairZeroInnerFiltration

open RealInducedPairLinkedReplacement in
/-- Actual adjacent filtration at zero signed inner weight, without a parity premise. -/
def RealInducedPairZeroInnerFiltrationStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ),
    0 < d.weight.natAbs → 0 < e.weight.natAbs → IsLinkedAt d e k →
      innerWeight d e k = 0 →
        RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)

theorem realInducedPairZeroInnerFiltration : RealInducedPairZeroInnerFiltrationStatement :=
  fun _ _ _ hd he h hH => RealInducedPairZeroInnerFiltration.filtration hd he h hH

end Langlands.Archimedean
