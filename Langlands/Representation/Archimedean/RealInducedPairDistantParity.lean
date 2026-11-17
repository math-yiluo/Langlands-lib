import Langlands.Representation.Archimedean.RealInducedPairDistantFiltration

/-! # Distant linked filtration with a free choice of internal parity -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairDistantParity

open RealStandardFiltration RealBlockFrobeniusMap RealBlockMultiplier
open RealCharacterPair RealCharacterPairReducible
open RealInducedPairAscendingExchange RealInducedPairLinkedReplacement

variable {d e : ComplexCharacterData} {k : ℕ} {sd se : Fin 2}

/-- Endpoint differences are independent of the internal quotient parities. -/
theorem differences (h : IsLinkedAt d e k) :
    (P.hi e se).exponent - (P.lo d sd).exponent = (outerWeight d e k : ℂ) ∧
    (P.lo e se).exponent - (P.lo d sd).exponent =
      (innerWeight d e k : ℂ) + (d.weight.natAbs : ℂ) ∧
    (P.hi e se).exponent - (P.hi d sd).exponent =
      (innerWeight d e k : ℂ) + (e.weight.natAbs : ℂ) ∧
    (P.lo e se).exponent - (P.hi d sd).exponent = (innerWeight d e k : ℂ) :=
  RealInducedPairDistantFiltration.differences h

/-- The outer reducible parity also makes the positive inner crossing reducible. -/
theorem inner_parity
    (hp : Even ((outerWeight d e k : ℤ) - 1 - pairParity (P.lo d sd) (P.hi e se)))
    (hH : 0 < innerWeight d e k) :
    Even (((innerWeight d e k).toNat : ℤ) - 1 -
      pairParity (P.hi d sd) (P.lo e se)) := by
  have hsum := RealInducedPairLinkedIncoming.weight_sum d e k
  have hcast : ((innerWeight d e k).toNat : ℤ) = innerWeight d e k :=
    Int.toNat_of_nonneg (by omega)
  simp only [pairParity, RealInducedPairQuotientPresentation.lo,
    RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData] at hp ⊢
  rw [Int.even_iff] at hp ⊢
  omega

/-- A generic middle multiplier on the actual parity class of any endpoint pair. -/
theorem exists_middle (c c' : RealCharacterData) {q : ℤ}
    (hp : Even (q - pairParity c c')) :
    ∃ μ : ℤ → ℂ, IsRecurrent ((q : ℂ) + 1) (pairParity c c') μ ∧
      IsSymmetric (pairParity c c') (sigma0 c c') μ ∧
      ∀ j, Even (j - pairParity c c') → μ j ≠ 0 := by
  let ε := (c.parity.val + c'.parity.val) % 2
  have hε : (ε : ℤ) = pairParity c c' := rfl
  obtain ⟨μ, hr, hs, hn⟩ := RealInducedPairGenericSwap.exists_multiplier ε
    (RealInducedPairLinkedIncoming.isGenericParameter_int ε (hε.symm ▸ hp))
  refine ⟨μ, hε ▸ hr, ?_, hε ▸ hn⟩
  simpa only [sigma0, ← hε, Int.natAbs_natCast] using hs

/-- The incoming ascending word for any compatible choice of internal parities. -/
theorem exists_ascendingData (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - 1 - pairParity (P.lo d sd) (P.hi e se)))
    (hH : 0 < innerWeight d e k) :
    ∃ μ₀ μ₂ : ℤ → ℂ,
      RealInducedPairAscendingExchange.MultiplierData e d se sd
        (binomialMultiplier (outerWeight d e k) (pairParity (P.lo d sd) (P.hi e se)))
        μ₀ μ₂
        (binomialMultiplier (innerWeight d e k).toNat (pairParity (P.hi d sd) (P.lo e se))) ∧
      (∀ j, Even (j - pairParity (P.lo d sd) (P.lo e se)) → μ₀ j ≠ 0) ∧
      (∀ j, Even (j - pairParity (P.hi d sd) (P.hi e se)) → μ₂ j ≠ 0) := by
  have hsum := RealInducedPairLinkedIncoming.weight_sum d e k
  have hcast : ((innerWeight d e k).toNat : ℤ) = innerWeight d e k :=
    Int.toNat_of_nonneg (by omega)
  have hcc : ((innerWeight d e k).toNat : ℂ) = (innerWeight d e k : ℂ) := by
    exact_mod_cast hcast
  have hp0 : Even (innerWeight d e k + (d.weight.natAbs : ℤ) -
      pairParity (P.lo d sd) (P.lo e se)) := by
    simp only [pairParity, RealInducedPairQuotientPresentation.lo,
      RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData] at hp ⊢
    rw [Int.even_iff] at hp ⊢
    omega
  have hp2 : Even (innerWeight d e k + (e.weight.natAbs : ℤ) -
      pairParity (P.hi d sd) (P.hi e se)) := by
    simp only [pairParity, RealInducedPairQuotientPresentation.lo,
      RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData] at hp ⊢
    rw [Int.even_iff] at hp ⊢
    omega
  obtain ⟨μ₀, hr0, hs0, hn0⟩ := exists_middle (P.lo d sd) (P.lo e se) hp0
  obtain ⟨μ₂, hr2, hs2, hn2⟩ := exists_middle (P.hi d sd) (P.hi e se) hp2
  obtain ⟨hν1, hν0, hν2, hν3⟩ := differences (sd := sd) (se := se) h
  refine ⟨μ₀, μ₂, ⟨?_, hs0, hs2, ?_, ?_, ?_, ?_, ?_⟩, hn0, hn2⟩
  · exact isSymmetric_binomialMultiplier _ (pairParity_eq _ _)
  · exact isSymmetric_binomialMultiplier _ (pairParity_eq _ _)
  · rw [hν1]
    exact isRecurrent_binomialMultiplier (RealInducedPairOuterTail.outerWeight_pos d e k)
      (pairParity_eq _ _) hp
  · rw [hν0]
    simpa only [Int.cast_add, Int.cast_natCast] using hr0
  · rw [hν2]
    simpa only [Int.cast_add, Int.cast_natCast] using hr2
  · rw [hν3, ← hcc]
    exact isRecurrent_binomialMultiplier (by omega) (pairParity_eq _ _) (inner_parity hp hH)

abbrev outerPiece (d e : ComplexCharacterData) (k : ℕ) (sd se : Fin 2) : List RealBlock :=
  [.character (P.lo e se),
    .induced (pairInduced (P.lo d sd) (P.hi e se) (outerWeight d e k)),
    .character (P.hi d sd)]

abbrev innerPiece (d e : ComplexCharacterData) (k : ℕ) (sd se : Fin 2) : List RealBlock :=
  [.character (P.lo d sd),
    .induced (pairInduced (P.hi d sd) (P.lo e se) (innerWeight d e k).toNat),
    .character (P.hi e se)]

/-- The natural positive inner weight is the last endpoint difference. -/
theorem inner_difference (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    (P.lo e se).exponent - (P.hi d sd).exponent = ((innerWeight d e k).toNat : ℂ) := by
  rw [(differences h).2.2.2]
  exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hH)).symm

/-- The binomial at the first crossing. -/
def outerBinomial (d e : ComplexCharacterData) (k : ℕ) (sd se : Fin 2) :
    KF 4 (P.X e d se sd) →ₗ[ℂ] KF 4 (X1 e d se sd) :=
  blockFrobMap (data_q0 (n := 4) (pre := [.character (P.lo e se)])
    (post := [.character (P.hi d sd)]) (c := P.lo d sd) (d := P.hi e se)
    (ℓ := outerWeight d e k) rfl)

/-- The binomial at the last crossing. -/
def innerBinomial (d e : ComplexCharacterData) (k : ℕ) (sd se : Fin 2) :
    KF 4 (X1 d e sd se) →ₗ[ℂ] KF 4 (P.X d e sd se) :=
  blockFrobMap (data_q0 (n := 4) (pre := [.character (P.lo d sd)])
    (post := [.character (P.hi e se)]) (c := P.hi d sd) (d := P.lo e se)
    (ℓ := (innerWeight d e k).toNat) rfl)

/-- The inverse-tail section of the outer fused block. -/
def outerSection (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - 1 - pairParity (P.lo d sd) (P.hi e se))) :
    KF 4 (outerPiece d e k sd se) →ₗ[ℂ] KF 4 (X1 e d se sd) :=
  blockFrobMap (data_q1 (n := 4) (pre := [.character (P.lo e se)])
    (post := [.character (P.hi d sd)]) rfl
    (RealInducedPairOuterTail.outerWeight_pos d e k) hp
    (differences h).1)

/-- The inverse-tail section of the inner fused block. -/
def innerSection (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - 1 - pairParity (P.lo d sd) (P.hi e se)))
    (hH : 0 < innerWeight d e k) :
    KF 4 (innerPiece d e k sd se) →ₗ[ℂ] KF 4 (P.X d e sd se) :=
  blockFrobMap (data_q1 (n := 4) (pre := [.character (P.lo d sd)])
    (post := [.character (P.hi e se)]) rfl (by omega)
    (inner_parity hp hH) (inner_difference h hH))

/-- The first two-piece decomposition in the incoming ascending word. -/
theorem outer_decomposition (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - 1 - pairParity (P.lo d sd) (P.hi e se))) :
    IsRealIntertwinerModulo 4 (outerPiece d e k sd se) (X1 e d se sd)
      (LinearMap.range (outerBinomial d e k sd se)) (outerSection h hp) ∧
    ∀ f, ∃ z r, outerBinomial d e k sd se z + outerSection h hp r = f :=
  RealInducedPairDistantFiltration.rankOne (n := 4) (pre := [.character (P.lo e se)])
    (post := [.character (P.hi d sd)]) rfl
    (RealInducedPairOuterTail.outerWeight_pos d e k) hp
    (differences h).1

/-- The last two-piece decomposition in the incoming ascending word. -/
theorem inner_decomposition (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - 1 - pairParity (P.lo d sd) (P.hi e se)))
    (hH : 0 < innerWeight d e k) :
    IsRealIntertwinerModulo 4 (innerPiece d e k sd se) (P.X d e sd se)
      (LinearMap.range (innerBinomial d e k sd se)) (innerSection h hp hH) ∧
    ∀ f, ∃ z r, innerBinomial d e k sd se z + innerSection h hp hH r = f :=
  RealInducedPairDistantFiltration.rankOne (n := 4) (pre := [.character (P.lo d sd)])
    (post := [.character (P.hi e se)]) rfl (by omega)
    (inner_parity hp hH) (inner_difference h hH)

/-- The last binomial is an exact intertwiner. -/
theorem innerBinomial_exact (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - 1 - pairParity (P.lo d sd) (P.hi e se)))
    (hH : 0 < innerWeight d e k) :
    IsRealIntertwinerModulo 4 (X1 d e sd se) (P.X d e sd se) ⊥
      (innerBinomial d e k sd se) :=
  RealInducedPairQuotientPresentation.binomial_exact (n := 4)
    (pre := [.character (P.lo d sd)]) (post := [.character (P.hi e se)]) rfl
    (by omega) (inner_parity hp hH) (inner_difference h hH)

section Middle

variable {μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ}
  (hm : RealInducedPairAscendingExchange.MultiplierData e d se sd μ₁ μ₀ μ₂ μ₃)

/-- The two disjoint middle crossings, in their specified order. -/
def middle : KF 4 (X1 e d se sd) →ₗ[ℂ] KF 4 (X1 d e sd se) :=
  (blockFrobMap hm.data20).comp (blockFrobMap hm.data0)

theorem middle_exact : IsRealIntertwinerModulo 4 (X1 e d se sd) (X1 d e sd se) ⊥
    (middle hm) :=
  modulo_comp_bot
    (swap_exact (n := 4) (pre := [.character (P.lo d sd), .character (P.lo e se)])
      (post := []) rfl hm.sym2 hm.rec2)
    (swap_exact (n := 4) (pre := [])
      (post := [.character (P.hi e se), .character (P.hi d sd)]) rfl hm.sym0 hm.rec0)

/-- Invert the two generic middle crossings on the full-character spaces. -/
theorem middle_surjective
    (hn0 : ∀ j, Even (j - pairParity (P.lo d sd) (P.lo e se)) → μ₀ j ≠ 0)
    (hn2 : ∀ j, Even (j - pairParity (P.hi d sd) (P.hi e se)) → μ₂ j ≠ 0) :
    Function.Surjective (middle hm) := by
  intro f
  let I₂ := blockFrobMap (data_unswap (n := 4)
    (pre := [.character (P.lo d sd), .character (P.lo e se)])
    (post := []) rfl hm.sym2)
  let I₀ := blockFrobMap (data_unswap (n := 4) (pre := [])
    (post := [.character (P.hi e se), .character (P.hi d sd)]) rfl hm.sym0)
  refine ⟨I₀ (I₂ f), ?_⟩
  change blockFrobMap hm.data20 (blockFrobMap hm.data0 (I₀ (I₂ f))) = f
  rw [RealCharacterInducedPushforward.frob_inv_of_ne_zero hm.data0 _ hn0]
  exact RealCharacterInducedPushforward.frob_inv_of_ne_zero hm.data20 _ hn2 f

end Middle

section CanonicalWord

variable {μ₀ μ₂ : ℤ → ℂ}
  (hm : RealInducedPairAscendingExchange.MultiplierData e d se sd
    (binomialMultiplier (outerWeight d e k) (pairParity (P.lo d sd) (P.hi e se)))
    μ₀ μ₂
    (binomialMultiplier (innerWeight d e k).toNat (pairParity (P.hi d sd) (P.lo e se))))

theorem first_eq : blockFrobMap hm.data1 = outerBinomial d e k sd se := rfl

theorem last_eq : blockFrobMap hm.data3 = innerBinomial d e k sd se := rfl

/-- The named binomials and middle composite are exactly the four crossings. -/
theorem crossings_eq : hm.crossings =
    (innerBinomial d e k sd se).comp ((middle hm).comp (outerBinomial d e k sd se)) := by
  unfold RealInducedPairAscendingExchange.MultiplierData.crossings
  rw [first_eq hm, last_eq hm]
  exact congrArg (fun F => (innerBinomial d e k sd se).comp F) (LinearMap.comp_assoc _ _ _).symm

/-- The assembled full-character map equals the map which descends. -/
theorem beforeDescent_eq (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) :
    hm.beforeDescent he hd = (P.quotientMap d e sd se hd he).comp
      ((innerBinomial d e k sd se).comp ((middle hm).comp (outerBinomial d e k sd se))) :=
  congrArg (fun F => (P.quotientMap d e sd se hd he).comp F) (crossings_eq hm)

end CanonicalWord

/-- The actual ascending exchange and the two fused sections span the target. -/
theorem filtration_of_pieces
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - 1 - pairParity (P.lo d sd) (P.hi e se)))
    (hH : 0 < innerWeight d e k)
    {C : List RealBlock → Prop}
    (hW : C [.induced e, .induced d])
    (hR : C (outerPiece d e k sd se)) (hU : C (innerPiece d e k sd se)) :
    HasFiltration 4 [.induced d, .induced e] C := by
  obtain ⟨μ₀, μ₂, hm, hn0, hn2⟩ := exists_ascendingData h hp hH
  obtain ⟨hq, hfac, hrange⟩ := hm.swap_descend he hd
  apply RealInducedPairDistantFiltration.assemble (P.quotientMap d e sd se hd he) (innerBinomial d e k sd se)
    ((middle hm).comp (outerBinomial d e k sd se)) ((middle hm).comp (outerSection h hp))
    (innerSection h hp hH) (hm.swap he hd) (P.quotientMap e d se sd he hd)
    (RealInducedPairQuotientPresentation.quotient_exact d e sd se hd he)
    (RealInducedPairQuotientPresentation.quotient_surjective d e sd se hd he)
    (innerBinomial_exact h hp hH)
    (RealInducedPairDistantFiltration.modulo_comp_range (middle_exact hm) (outer_decomposition h hp).1)
    (inner_decomposition h hp hH).1 hq ?_ ?_
    (RealInducedPairDistantFiltration.span_comp (middle hm) _ _ (middle_surjective hm hn0 hn2) (outer_decomposition h hp).2)
    (inner_decomposition h hp hH).2 hW hR hU
  · exact hfac.trans (beforeDescent_eq hm hd he)
  · exact hrange.trans (congrArg LinearMap.range (beforeDescent_eq hm hd he))

/-- Internal parities do not alter endpoint support. -/
theorem outer_support (h : IsLinkedAt d e k) :
    (realExponentSupport (outerPiece d e k sd se)).Perm
      (realExponentSupport [.induced d, .induced e]) :=
  RealInducedPairDistantFiltration.outer_support h

theorem inner_support (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    (realExponentSupport (innerPiece d e k sd se)).Perm
      (realExponentSupport [.induced d, .induced e]) :=
  RealInducedPairDistantFiltration.inner_support h hH

@[simp] theorem outer_weightSquareSum (d e : ComplexCharacterData) (k : ℕ) (sd se : Fin 2) :
    realWeightSquareSum (outerPiece d e k sd se) = outerWeight d e k ^ 2 := by
  simp [outerPiece, realWeightSquareSum, realBlockWeightSquare]

@[simp] theorem inner_weightSquareSum (d e : ComplexCharacterData) (k : ℕ) (sd se : Fin 2) :
    realWeightSquareSum (innerPiece d e k sd se) = (innerWeight d e k).toNat ^ 2 := by
  simp only [innerPiece, realWeightSquareSum, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, realBlockWeightSquare, pairInduced_weight,
    Int.natAbs_natCast, zero_add, add_zero]

/-- A freely chosen parity makes both singular crossings compatible. -/
def selectedParity (d e : ComplexCharacterData) (k : ℕ) : Fin 2 :=
  ⟨(outerWeight d e k + e.weight.natAbs) % 2, Nat.mod_lt _ two_pos⟩

theorem selectedParity_outer (d e : ComplexCharacterData) (k : ℕ) :
    Even ((outerWeight d e k : ℤ) - 1 -
      pairParity (P.lo d 0) (P.hi e (selectedParity d e k))) := by
  simp only [pairParity, RealInducedPairQuotientPresentation.lo,
    RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData,
    selectedParity, Fin.val_zero, zero_add]
  rw [Int.even_iff]
  omega

/-- No parity assumption on the original two blocks is needed in the distant region. -/
theorem filtration (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k)
    (hb : d.weight.natAbs ^ 2 + e.weight.natAbs ^ 2 < (innerWeight d e k).toNat ^ 2) :
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e) := by
  have hH : 0 < innerWeight d e k := by
    by_contra hH
    have hz : (innerWeight d e k).toNat = 0 := by omega
    simp only [hz, zero_pow two_ne_zero] at hb
    omega
  have hHP : (innerWeight d e k).toNat < outerWeight d e k := by
    have hsum := RealInducedPairLinkedIncoming.weight_sum d e k
    have hcast := Int.toNat_of_nonneg (le_of_lt hH)
    omega
  have hP : d.weight.natAbs ^ 2 + e.weight.natAbs ^ 2 < outerWeight d e k ^ 2 :=
    hb.trans (Nat.pow_lt_pow_left hHP two_ne_zero)
  apply (realAdjacentFiltration_iff 4 [] [] (.induced d) (.induced e)).mpr
  apply filtration_of_pieces (sd := 0) (se := selectedParity d e k) hd he h
    (selectedParity_outer d e k) hH
  · exact ⟨[.induced e, .induced d], rfl, Or.inl rfl⟩
  · refine ⟨outerPiece d e k 0 (selectedParity d e k), rfl, Or.inr ⟨outer_support h, ?_⟩⟩
    rw [outer_weightSquareSum]
    simpa [realWeightSquareSum, realBlockWeightSquare] using hP
  · refine ⟨innerPiece d e k 0 (selectedParity d e k), rfl, Or.inr ⟨inner_support h hH, ?_⟩⟩
    rw [inner_weightSquareSum]
    simpa [realWeightSquareSum, realBlockWeightSquare] using hb

end RealInducedPairDistantParity

open RealInducedPairLinkedReplacement in
/-- The distant linked adjacent filtration for both parity classes of the gap. -/
def RealInducedPairDistantParityFiltrationStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ),
    0 < d.weight.natAbs → 0 < e.weight.natAbs → IsLinkedAt d e k →
      d.weight.natAbs ^ 2 + e.weight.natAbs ^ 2 < (innerWeight d e k).toNat ^ 2 →
        RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)

theorem realInducedPairDistantParityFiltration : RealInducedPairDistantParityFiltrationStatement :=
  fun _ _ _ hd he h hb => RealInducedPairDistantParity.filtration hd he h hb

end Langlands.Archimedean
