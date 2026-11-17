import Langlands.Representation.Archimedean.RealInducedPairDistantParity

/-! # Linked exchange with singular middle crossings -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairMiddleParity

open RealStandardFiltration RealBlockFrobeniusMap RealBlockMultiplier
open RealCharacterPair RealCharacterPairReducible
open RealInducedPairAscendingExchange RealInducedPairLinkedReplacement

def lowerWeight (d e : ComplexCharacterData) (k : ℕ) : ℕ :=
  outerWeight d e k - e.weight.natAbs

def upperWeight (d e : ComplexCharacterData) (k : ℕ) : ℕ :=
  outerWeight d e k - d.weight.natAbs

theorem weight_id (d e : ComplexCharacterData) (k : ℕ) :
    (lowerWeight d e k : ℤ) = innerWeight d e k + d.weight.natAbs ∧
    (upperWeight d e k : ℤ) = innerWeight d e k + e.weight.natAbs := by
  have hs := RealInducedPairLinkedIncoming.weight_sum d e k
  have hd := le_max_left d.weight.natAbs e.weight.natAbs
  have he := le_max_right d.weight.natAbs e.weight.natAbs
  dsimp [lowerWeight, upperWeight, outerWeight] at *
  omega

theorem gap_le (d e : ComplexCharacterData) (k : ℕ) :
    k + 1 ≤ lowerWeight d e k ∧ k + 1 ≤ upperWeight d e k := by
  have hd := le_max_left d.weight.natAbs e.weight.natAbs
  have he := le_max_right d.weight.natAbs e.weight.natAbs
  dsimp [lowerWeight, upperWeight, outerWeight]
  omega

theorem weights_pos (d e : ComplexCharacterData) (k : ℕ) :
    0 < lowerWeight d e k ∧ 0 < upperWeight d e k := by
  have hg := gap_le d e k
  omega

variable {d e : ComplexCharacterData} {k : ℕ} {sd se : Fin 2}

theorem lower_difference (h : IsLinkedAt d e k) :
    (P.lo e se).exponent - (P.lo d sd).exponent = (lowerWeight d e k : ℂ) := by
  rw [(RealInducedPairDistantParity.differences h).2.1]
  simpa only [Int.cast_add, Int.cast_natCast] using
    congrArg (fun z : ℤ => (z : ℂ)) (weight_id d e k).1.symm

theorem upper_difference (h : IsLinkedAt d e k) :
    (P.hi e se).exponent - (P.hi d sd).exponent = (upperWeight d e k : ℂ) := by
  rw [(RealInducedPairDistantParity.differences h).2.2.1]
  simpa only [Int.cast_add, Int.cast_natCast] using
    congrArg (fun z : ℤ => (z : ℂ)) (weight_id d e k).2.symm

theorem parities
    (hp : Even ((outerWeight d e k : ℤ) - pairParity (P.lo d sd) (P.hi e se))) :
    Even ((lowerWeight d e k : ℤ) - 1 - pairParity (P.lo d sd) (P.lo e se)) ∧
    Even ((upperWeight d e k : ℤ) - 1 - pairParity (P.hi d sd) (P.hi e se)) ∧
    Even (innerWeight d e k - pairParity (P.hi d sd) (P.lo e se)) := by
  have hs := RealInducedPairLinkedIncoming.weight_sum d e k
  have hw := weight_id d e k
  simp only [pairParity, RealInducedPairQuotientPresentation.lo,
    RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData] at hp ⊢
  rw [Int.even_iff] at hp
  simp only [Int.even_iff]
  omega

/-- The first and last crossings are generic; the middle crossings are binomial. -/
theorem exists_ascendingData (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - pairParity (P.lo d sd) (P.hi e se))) :
    ∃ μ₁ μ₃ : ℤ → ℂ,
      MultiplierData e d se sd μ₁
        (binomialMultiplier (lowerWeight d e k) (pairParity (P.lo d sd) (P.lo e se)))
        (binomialMultiplier (upperWeight d e k) (pairParity (P.hi d sd) (P.hi e se))) μ₃ ∧
      (∀ j, Even (j - pairParity (P.lo d sd) (P.hi e se)) → μ₁ j ≠ 0) ∧
      (∀ j, Even (j - pairParity (P.hi d sd) (P.lo e se)) → μ₃ j ≠ 0) := by
  obtain ⟨hp0, hp2, hp3⟩ := parities hp
  obtain ⟨μ₁, hr1, hs1, hn1⟩ :=
    RealInducedPairDistantParity.exists_middle (P.lo d sd) (P.hi e se) hp
  obtain ⟨μ₃, hr3, hs3, hn3⟩ :=
    RealInducedPairDistantParity.exists_middle (P.hi d sd) (P.lo e se) hp3
  refine ⟨μ₁, μ₃, ⟨hs1, ?_, ?_, hs3, ?_, ?_, ?_, ?_⟩, hn1, hn3⟩
  · exact isSymmetric_binomialMultiplier _ (pairParity_eq _ _)
  · exact isSymmetric_binomialMultiplier _ (pairParity_eq _ _)
  · rw [(RealInducedPairDistantParity.differences h).1]
    simpa only [Int.cast_natCast] using hr1
  · rw [lower_difference h]
    exact isRecurrent_binomialMultiplier (weights_pos d e k).1 (pairParity_eq _ _) hp0
  · rw [upper_difference h]
    exact isRecurrent_binomialMultiplier (weights_pos d e k).2 (pairParity_eq _ _) hp2
  · rw [(RealInducedPairDistantParity.differences h).2.2.2]
    exact hr3

abbrev lowerPiece (d e : ComplexCharacterData) (k : ℕ) (sd se : Fin 2) : List RealBlock :=
  [.induced (pairInduced (P.lo d sd) (P.lo e se) (lowerWeight d e k)),
    .character (P.hi e se), .character (P.hi d sd)]

abbrev upperPiece (d e : ComplexCharacterData) (k : ℕ) (sd se : Fin 2) : List RealBlock :=
  [.character (P.lo d sd), .character (P.lo e se),
    .induced (pairInduced (P.hi d sd) (P.hi e se) (upperWeight d e k))]

def lowerBinomial (d e : ComplexCharacterData) (k : ℕ) (sd se : Fin 2) :
    KF 4 (X1 e d se sd) →ₗ[ℂ] KF 4 (X10 e d se sd) :=
  blockFrobMap (data_q0 (n := 4) (pre := [])
    (post := [.character (P.hi e se), .character (P.hi d sd)])
    (c := P.lo d sd) (d := P.lo e se) (ℓ := lowerWeight d e k) rfl)

def upperBinomial (d e : ComplexCharacterData) (k : ℕ) (sd se : Fin 2) :
    KF 4 (X10 e d se sd) →ₗ[ℂ] KF 4 (X1 d e sd se) :=
  blockFrobMap (data_q0 (n := 4)
    (pre := [.character (P.lo d sd), .character (P.lo e se)]) (post := [])
    (c := P.hi d sd) (d := P.hi e se) (ℓ := upperWeight d e k) rfl)

def lowerSection (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - pairParity (P.lo d sd) (P.hi e se))) :
    KF 4 (lowerPiece d e k sd se) →ₗ[ℂ] KF 4 (X10 e d se sd) :=
  blockFrobMap (data_q1 (n := 4) (pre := [])
    (post := [.character (P.hi e se), .character (P.hi d sd)])
    rfl (weights_pos d e k).1 (parities hp).1 (lower_difference h))

def upperSection (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - pairParity (P.lo d sd) (P.hi e se))) :
    KF 4 (upperPiece d e k sd se) →ₗ[ℂ] KF 4 (X1 d e sd se) :=
  blockFrobMap (data_q1 (n := 4)
    (pre := [.character (P.lo d sd), .character (P.lo e se)]) (post := [])
    rfl (weights_pos d e k).2 (parities hp).2.1 (upper_difference h))

theorem lower_decomposition (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - pairParity (P.lo d sd) (P.hi e se))) :
    IsRealIntertwinerModulo 4 (lowerPiece d e k sd se) (X10 e d se sd)
      (LinearMap.range (lowerBinomial d e k sd se)) (lowerSection h hp) ∧
    ∀ f, ∃ z r, lowerBinomial d e k sd se z + lowerSection h hp r = f :=
  RealInducedPairDistantFiltration.rankOne (n := 4) (pre := [])
    (post := [.character (P.hi e se), .character (P.hi d sd)]) rfl
    (weights_pos d e k).1 (parities hp).1 (lower_difference h)

theorem upper_decomposition (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - pairParity (P.lo d sd) (P.hi e se))) :
    IsRealIntertwinerModulo 4 (upperPiece d e k sd se) (X1 d e sd se)
      (LinearMap.range (upperBinomial d e k sd se)) (upperSection h hp) ∧
    ∀ f, ∃ z r, upperBinomial d e k sd se z + upperSection h hp r = f :=
  RealInducedPairDistantFiltration.rankOne (n := 4)
    (pre := [.character (P.lo d sd), .character (P.lo e se)]) (post := []) rfl
    (weights_pos d e k).2 (parities hp).2.1 (upper_difference h)

theorem upperBinomial_exact (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - pairParity (P.lo d sd) (P.hi e se))) :
    IsRealIntertwinerModulo 4 (X10 e d se sd) (X1 d e sd se) ⊥
      (upperBinomial d e k sd se) :=
  RealInducedPairQuotientPresentation.binomial_exact (n := 4)
    (pre := [.character (P.lo d sd), .character (P.lo e se)]) (post := []) rfl
    (weights_pos d e k).2 (parities hp).2.1 (upper_difference h)

section Word

variable {μ₁ μ₃ : ℤ → ℂ}
  (hm : MultiplierData e d se sd μ₁
    (binomialMultiplier (lowerWeight d e k) (pairParity (P.lo d sd) (P.lo e se)))
    (binomialMultiplier (upperWeight d e k) (pairParity (P.hi d sd) (P.hi e se))) μ₃)

def inverseFirst : KF 4 (X1 e d se sd) →ₗ[ℂ] KF 4 (P.X e d se sd) :=
  blockFrobMap (data_unswap (n := 4) (pre := [.character (P.lo e se)])
    (post := [.character (P.hi d sd)]) rfl hm.sym1)

theorem first_inverse
    (hn : ∀ j, Even (j - pairParity (P.lo d sd) (P.hi e se)) → μ₁ j ≠ 0)
    (f : KF 4 (X1 e d se sd)) :
    blockFrobMap hm.data1 (inverseFirst hm f) = f :=
  RealCharacterInducedPushforward.frob_inv_of_ne_zero hm.data1 _ hn f

theorem first_surjective
    (hn : ∀ j, Even (j - pairParity (P.lo d sd) (P.hi e se)) → μ₁ j ≠ 0) :
    Function.Surjective (blockFrobMap hm.data1) :=
  fun f => ⟨inverseFirst hm f, first_inverse hm hn f⟩

theorem last_surjective
    (hn : ∀ j, Even (j - pairParity (P.hi d sd) (P.lo e se)) → μ₃ j ≠ 0) :
    Function.Surjective (blockFrobMap hm.data3) := by
  intro f
  let I := blockFrobMap (data_unswap (n := 4) (pre := [.character (P.lo d sd)])
    (post := [.character (P.hi e se)]) rfl hm.sym3)
  exact ⟨I f, RealCharacterInducedPushforward.frob_inv_of_ne_zero hm.data3 _ hn f⟩

theorem lower_eq : blockFrobMap hm.data0 = lowerBinomial d e k sd se := rfl
theorem upper_eq : blockFrobMap hm.data20 = upperBinomial d e k sd se := rfl

theorem crossings_eq :
    hm.crossings = (blockFrobMap hm.data3).comp
      (((upperBinomial d e k sd se).comp (lowerBinomial d e k sd se)).comp
        (blockFrobMap hm.data1)) := by
  unfold MultiplierData.crossings
  rw [lower_eq hm, upper_eq hm]
  exact congrArg (fun F => (blockFrobMap hm.data3).comp F)
    (LinearMap.comp_assoc (blockFrobMap hm.data1) (lowerBinomial d e k sd se)
      (upperBinomial d e k sd se)).symm

end Word

/-- The alternate parity word supplies an actual three-piece filtration. -/
theorem filtration_of_pieces
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - pairParity (P.lo d sd) (P.hi e se)))
    {C : List RealBlock → Prop}
    (hW : C [.induced e, .induced d])
    (hR : C (lowerPiece d e k sd se)) (hU : C (upperPiece d e k sd se)) :
    HasFiltration 4 [.induced d, .induced e] C := by
  obtain ⟨μ₁, μ₃, hm, hn1, hn3⟩ := exists_ascendingData h hp
  let A := (P.quotientMap d e sd se hd he).comp (blockFrobMap hm.data3)
  let π := (P.quotientMap e d se sd he hd).comp (inverseFirst hm)
  have hA : IsRealIntertwinerModulo 4 (X1 d e sd se) [.induced d, .induced e] ⊥ A :=
    modulo_comp_bot (RealInducedPairQuotientPresentation.quotient_exact d e sd se hd he)
      (swap_exact (n := 4) (pre := [.character (P.lo d sd)])
        (post := [.character (P.hi e se)]) rfl hm.sym3 hm.rec3)
  have hAs : Function.Surjective A :=
    (RealInducedPairQuotientPresentation.quotient_surjective d e sd se hd he).comp
      (last_surjective hm hn3)
  have hbefore : hm.beforeDescent he hd =
      (A.comp ((upperBinomial d e k sd se).comp (lowerBinomial d e k sd se))).comp
        (blockFrobMap hm.data1) := by
    unfold MultiplierData.beforeDescent
    rw [crossings_eq hm]
    exact ((LinearMap.comp_assoc
      (((upperBinomial d e k sd se).comp (lowerBinomial d e k sd se)).comp
        (blockFrobMap hm.data1))
      (blockFrobMap hm.data3) (P.quotientMap d e sd se hd he)).symm).trans
      (LinearMap.comp_assoc (blockFrobMap hm.data1)
        ((upperBinomial d e k sd se).comp (lowerBinomial d e k sd se))
        A).symm
  obtain ⟨hq, hfac, hrange⟩ := hm.swap_descend he hd
  have hfac' : (hm.swap he hd).comp π =
      A.comp ((upperBinomial d e k sd se).comp (lowerBinomial d e k sd se)) := by
    apply LinearMap.ext
    intro f
    have hf := LinearMap.congr_fun hfac (inverseFirst hm f)
    rw [hbefore] at hf
    change (hm.swap he hd) (P.quotientMap e d se sd he hd (inverseFirst hm f)) =
      A (upperBinomial d e k sd se (lowerBinomial d e k sd se
        (blockFrobMap hm.data1 (inverseFirst hm f)))) at hf
    rw [first_inverse hm hn1] at hf
    exact hf
  have hrange' : LinearMap.range (hm.swap he hd) =
      LinearMap.range (A.comp ((upperBinomial d e k sd se).comp
        (lowerBinomial d e k sd se))) := by
    rw [hbefore] at hrange
    exact hrange.trans (LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (first_surjective hm hn1)))
  exact RealInducedPairDistantFiltration.assemble A (upperBinomial d e k sd se)
    (lowerBinomial d e k sd se) (lowerSection h hp) (upperSection h hp)
    (hm.swap he hd) π hA hAs (upperBinomial_exact h hp)
    (lower_decomposition h hp).1 (upper_decomposition h hp).1 hq hfac' hrange'
    (lower_decomposition h hp).2 (upper_decomposition h hp).2 hW hR hU

theorem lower_support_eq (h : IsLinkedAt d e k) :
    realExponentSupport (lowerPiece d e k sd se) =
      [(P.lo e se).exponent, (P.lo d sd).exponent,
        (P.hi e se).exponent, (P.hi d sd).exponent] := by
  change realExponentSupport [.induced
    (pairInduced (P.lo d sd) (P.lo e se) (lowerWeight d e k))] ++
      [(P.hi e se).exponent, (P.hi d sd).exponent] = _
  rw [realExponentSupport_pairInduced_eq (lower_difference h)]
  rfl

theorem upper_support_eq (h : IsLinkedAt d e k) :
    realExponentSupport (upperPiece d e k sd se) =
      [(P.lo d sd).exponent, (P.lo e se).exponent,
        (P.hi e se).exponent, (P.hi d sd).exponent] := by
  change [(P.lo d sd).exponent, (P.lo e se).exponent] ++
    realExponentSupport [.induced
      (pairInduced (P.hi d sd) (P.hi e se) (upperWeight d e k))] = _
  rw [realExponentSupport_pairInduced_eq (upper_difference h)]
  rfl

theorem lower_support (h : IsLinkedAt d e k) :
    (realExponentSupport (lowerPiece d e k sd se)).Perm
      (realExponentSupport [.induced d, .induced e]) := by
  rw [lower_support_eq h]
  change [(P.lo e se).exponent, (P.lo d sd).exponent,
    (P.hi e se).exponent, (P.hi d sd).exponent].Perm
    [(P.hi d sd).exponent, (P.lo d sd).exponent,
      (P.hi e se).exponent, (P.lo e se).exponent]
  exact (List.reverse_perm _).symm.trans ((List.Perm.swap _ _ [_]).cons _)

theorem upper_support (h : IsLinkedAt d e k) :
    (realExponentSupport (upperPiece d e k sd se)).Perm
      (realExponentSupport [.induced d, .induced e]) := by
  have hh := lower_support (sd := sd) (se := se) h
  rw [lower_support_eq h] at hh
  rw [upper_support_eq h]
  exact (List.Perm.swap _ _ _).trans hh

@[simp] theorem lower_weightSquareSum (d e : ComplexCharacterData) (k : ℕ) (sd se : Fin 2) :
    realWeightSquareSum (lowerPiece d e k sd se) = lowerWeight d e k ^ 2 := by
  simp [lowerPiece, realWeightSquareSum, realBlockWeightSquare]

@[simp] theorem upper_weightSquareSum (d e : ComplexCharacterData) (k : ℕ) (sd se : Fin 2) :
    realWeightSquareSum (upperPiece d e k sd se) = upperWeight d e k ^ 2 := by
  simp [upperPiece, realWeightSquareSum, realBlockWeightSquare]

/-- The alternate internal parity puts both singular crossings in the middle. -/
def selectedParity (d e : ComplexCharacterData) (k : ℕ) : Fin 2 :=
  ⟨(outerWeight d e k + e.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩

theorem selectedParity_outer (d e : ComplexCharacterData) (k : ℕ) :
    Even ((outerWeight d e k : ℤ) -
      pairParity (P.lo d 0) (P.hi e (selectedParity d e k))) := by
  simp only [pairParity, RealInducedPairQuotientPresentation.lo,
    RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData,
    selectedParity, Fin.val_zero, zero_add]
  rw [Int.even_iff]
  omega

/-- The natural gap bound makes both middle fused source lists strictly heavier. -/
theorem filtration (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k)
    (hb : d.weight.natAbs ^ 2 + e.weight.natAbs ^ 2 < (k + 1) ^ 2) :
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e) := by
  have hA : d.weight.natAbs ^ 2 + e.weight.natAbs ^ 2 < lowerWeight d e k ^ 2 :=
    hb.trans_le (Nat.pow_le_pow_left (gap_le d e k).1 2)
  have hB : d.weight.natAbs ^ 2 + e.weight.natAbs ^ 2 < upperWeight d e k ^ 2 :=
    hb.trans_le (Nat.pow_le_pow_left (gap_le d e k).2 2)
  apply (realAdjacentFiltration_iff 4 [] [] (.induced d) (.induced e)).mpr
  apply filtration_of_pieces (sd := 0) (se := selectedParity d e k) hd he h
    (selectedParity_outer d e k)
  · exact ⟨[.induced e, .induced d], rfl, Or.inl rfl⟩
  · refine ⟨lowerPiece d e k 0 (selectedParity d e k), rfl, Or.inr ⟨lower_support h, ?_⟩⟩
    rw [lower_weightSquareSum]
    simpa [realWeightSquareSum, realBlockWeightSquare] using hA
  · refine ⟨upperPiece d e k 0 (selectedParity d e k), rfl, Or.inr ⟨upper_support h, ?_⟩⟩
    rw [upper_weightSquareSum]
    simpa [realWeightSquareSum, realBlockWeightSquare] using hB

end RealInducedPairMiddleParity

open RealInducedPairLinkedReplacement in
/-- The actual linked filtration when the natural gap square exceeds the original sum. -/
def RealInducedPairMiddleParityFiltrationStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ),
    0 < d.weight.natAbs → 0 < e.weight.natAbs → IsLinkedAt d e k →
      d.weight.natAbs ^ 2 + e.weight.natAbs ^ 2 < (k + 1) ^ 2 →
        RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)

theorem realInducedPairMiddleParityFiltration : RealInducedPairMiddleParityFiltrationStatement :=
  fun _ _ _ hd he h hb => RealInducedPairMiddleParity.filtration hd he h hb

end Langlands.Archimedean
