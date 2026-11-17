import Langlands.Representation.Archimedean.RealInducedPairAscendingExchange
import Langlands.Representation.Archimedean.RealInducedPairLinkedIncoming

/-! # Filtration at sufficiently distant linked real induction blocks -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairDistantFiltration

open RealStandardFiltration RealBlockFrobeniusMap RealBlockMultiplier
open RealCharacterPair RealCharacterPairReducible
open RealInducedPairAscendingExchange RealInducedPairLinkedReplacement

section Assembly

variable {n : ℕ} {V X Y Z W R U : List RealBlock}

/-- Two successive two-piece decompositions, with descent of the first map. -/
theorem assemble
    (A : KF n X →ₗ[ℂ] KF n V)
    (G : KF n Y →ₗ[ℂ] KF n X)
    (F : KF n Z →ₗ[ℂ] KF n Y)
    (s : KF n R →ₗ[ℂ] KF n Y)
    (t : KF n U →ₗ[ℂ] KF n X)
    (q : KF n W →ₗ[ℂ] KF n V)
    (π : KF n Z →ₗ[ℂ] KF n W)
    (hA : IsRealIntertwinerModulo n X V ⊥ A)
    (hAs : Function.Surjective A)
    (hG : IsRealIntertwinerModulo n Y X ⊥ G)
    (hs : IsRealIntertwinerModulo n R Y (LinearMap.range F) s)
    (ht : IsRealIntertwinerModulo n U X (LinearMap.range G) t)
    (hq : IsRealIntertwinerModulo n W V ⊥ q)
    (hfac : q.comp π = A.comp (G.comp F))
    (hrange : LinearMap.range q = LinearMap.range (A.comp (G.comp F)))
    (hY : ∀ y, ∃ z r, F z + s r = y)
    (hX : ∀ x, ∃ y u, G y + t u = x)
    {P : List RealBlock → Prop} (hW : P W) (hR : P R) (hU : P U) :
    HasFiltration n V P := by
  let qR := A.comp (G.comp s)
  let qU := A.comp t
  have hqR : IsRealIntertwinerModulo n R V (LinearMap.range q) qR := by
    have hh := modulo_comp (modulo_comp_bot hA hG) hs
    apply modulo_mono hh
    rw [bot_sup_eq, ← LinearMap.range_comp, hrange]
    exact le_of_eq (by congr 1)
  have hAG : LinearMap.range (A.comp G) ≤ LinearMap.range q ⊔ LinearMap.range qR := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, r, hz⟩ := hY y
    rw [← hz, LinearMap.comp_apply, map_add, map_add]
    apply Submodule.add_mem
    · apply Submodule.mem_sup_left
      exact ⟨π z, LinearMap.congr_fun hfac z⟩
    · exact Submodule.mem_sup_right ⟨r, rfl⟩
  have hqU : IsRealIntertwinerModulo n U V
      (LinearMap.range q ⊔ LinearMap.range qR) qU := by
    apply modulo_mono (modulo_comp hA ht)
    rw [bot_sup_eq, ← LinearMap.range_comp]
    exact hAG
  let es : Fin 3 → List RealBlock := ![W, R, U]
  let qs : ∀ j : Fin 3, KF n (es j) →ₗ[ℂ] KF n V :=
    Fin.cons (α := fun j : Fin 3 => KF n (es j) →ₗ[ℂ] KF n V)
      q (Fin.cons qR (Fin.cons qU finZeroElim))
  refine ⟨Fin 3, inferInstance, inferInstance, es, qs, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hW
    · exact hR
    · exact hU
  · intro j
    fin_cases j
    · exact modulo_mono hq bot_le
    · exact modulo_mono hqR
        (le_iSup₂_of_le (f := fun (i : Fin 3) (_ : i < 1) =>
          LinearMap.range (qs i)) 0 (by decide) le_rfl)
    · apply modulo_mono hqU
      apply sup_le
      · exact le_iSup₂_of_le (f := fun (i : Fin 3) (_ : i < 2) =>
          LinearMap.range (qs i)) 0 (by decide) le_rfl
      · exact le_iSup₂_of_le (f := fun (i : Fin 3) (_ : i < 2) =>
          LinearMap.range (qs i)) 1 (by decide) le_rfl
  · apply eq_top_iff.mpr
    intro v _
    obtain ⟨x, rfl⟩ := hAs v
    obtain ⟨y, u, hx⟩ := hX x
    obtain ⟨z, r, hy⟩ := hY y
    have heq : A x = q (π z) + qR r + qU u := by
      rw [← hx, ← hy, map_add, map_add, map_add]
      rw [show q (π z) = A (G (F z)) from LinearMap.congr_fun hfac z]
      rfl
    rw [heq]
    exact add_mem
      (add_mem (Submodule.mem_iSup_of_mem (0 : Fin 3) ⟨π z, rfl⟩)
        (Submodule.mem_iSup_of_mem (1 : Fin 3) ⟨r, rfl⟩))
      (Submodule.mem_iSup_of_mem (2 : Fin 3) ⟨u, rfl⟩)

end Assembly

section RankOne

variable {n : ℕ} {pre post : List RealBlock} {c c' : RealCharacterData} {ℓ : ℕ}

/-- The two maps of a positive rank-one decomposition, including their spanning identity. -/
theorem rankOne
    (hn : realRank (pre ++ .character c :: .character c' :: post) = n)
    (hℓ : 0 < ℓ) (hp : Even ((ℓ : ℤ) - 1 - pairParity c c'))
    (hν : c'.exponent - c.exponent = ℓ) :
    IsRealIntertwinerModulo n (pre ++ indBlock c c' ℓ ++ post)
      (pre ++ .character c :: .character c' :: post)
      (LinearMap.range (blockFrobMap (data_q0 (ℓ := ℓ) hn)))
      (blockFrobMap (data_q1 hn hℓ hp hν)) ∧
    ∀ f, ∃ z r,
      blockFrobMap (data_q0 (ℓ := ℓ) hn) z +
        blockFrobMap (data_q1 hn hℓ hp hν) r = f := by
  have hD := data_D hn hℓ hp hν
  have hS := data_q1 hn hℓ hp hν
  have hQ := data_q0 (ℓ := ℓ) hn
  have hB := data_B (ℓ := ℓ) hn
  have hind : realInducedBlockAt (pre ++ indBlock c c' ℓ ++ post) (realRank pre) =
      some (pairInduced c c' ℓ) := by
    have hh := RealBlockPosition.realInducedBlockAt_mid pre (indBlock c c' ℓ) post
      (j := 0) two_pos
    simpa only [add_zero] using hh.trans (show
      realInducedBlockAt (indBlock c c' ℓ) 0 = some (pairInduced c c' ℓ) from rfl)
  have hinv : ∀ r, blockFrobMap hD (blockFrobMap hS r) = r :=
    RealCharacterInducedPushforward.tail_inv hℓ (pairParity_eq c c') hp
      (neg_one_pow_sq_fin c'.parity) hD hS hind
      (by rw [pairInduced_weight, abs_of_nonneg (Int.natCast_nonneg _)])
  have hker : LinearMap.ker (blockFrobMap hD) ≤ LinearMap.range (blockFrobMap hQ) :=
    RealCharacterInducedPushforward.ker_tail_le_range hℓ (pairParity_eq c c') hp
      (neg_one_pow_sq_fin c'.parity) hQ hB hD
  have hrec : IsRecurrent
      (GramFormula.realPositionExponent
          (pre ++ .character c :: .character c' :: post) (realRank pre) -
        GramFormula.realPositionExponent
          (pre ++ .character c :: .character c' :: post) (realRank pre + 1) + 1)
      (pairParity c c') (tailMultiplier ℓ (pairParity c c') ((-1) ^ c'.parity.val)) := by
    have h0 : GramFormula.realPositionExponent
        (pre ++ .character c :: .character c' :: post) (realRank pre) = c.exponent := by
      rw [← mid_pair pre post (.character c) (.character c'),
        exponent_mid_zero pre post (realRank_cd (c := c) (d := c') ▸ two_pos)]
      rfl
    have h1 : GramFormula.realPositionExponent
        (pre ++ .character c :: .character c' :: post) (realRank pre + 1) = c'.exponent := by
      rw [← mid_pair pre post (.character c) (.character c'),
        exponent_mid_one pre post (realRank_cd (c := c) (d := c') ▸ one_lt_two)]
      rfl
    rw [h0, h1, show c.exponent - c'.exponent + 1 = 1 - (ℓ : ℂ) by
      linear_combination -hν]
    exact isRecurrent_tailMultiplier hℓ (pairParity_eq c c') hp
      (neg_one_pow_sq_fin c'.parity)
  refine ⟨isRealIntertwinerModulo_of_leftInverse hS hD hrec hinv _ hker, ?_⟩
  intro f
  have hf : f - blockFrobMap hS (blockFrobMap hD f) ∈ LinearMap.ker (blockFrobMap hD) := by
    rw [LinearMap.mem_ker, map_sub, hinv, sub_self]
  obtain ⟨z, hz⟩ := hker hf
  exact ⟨z, blockFrobMap hD f, by rw [hz]; abel⟩

end RankOne

section Parameters

variable {d e : ComplexCharacterData} {k : ℕ}

/-- The four positive incoming differences, expressed in the linked weights. -/
theorem differences (h : IsLinkedAt d e k) :
    (P.hi e 0).exponent - (P.lo d 0).exponent = (outerWeight d e k : ℂ) ∧
    (P.lo e 0).exponent - (P.lo d 0).exponent =
      (innerWeight d e k : ℂ) + (d.weight.natAbs : ℂ) ∧
    (P.hi e 0).exponent - (P.hi d 0).exponent =
      (innerWeight d e k : ℂ) + (e.weight.natAbs : ℂ) ∧
    (P.lo e 0).exponent - (P.hi d 0).exponent = (innerWeight d e k : ℂ) := by
  obtain ⟨h1, h2, h3, h4⟩ := endpoint_equalities h
  dsimp [RealInducedPairQuotientPresentation.lo, RealInducedPairQuotientPresentation.hi,
    RealJacquetFrobenius.charData]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination -h1 + h2
  · linear_combination -h3 + h4
  · linear_combination -h3 + h4
  · linear_combination -h3 + h4

/-- Actual middle parity at the upper endpoints. -/
theorem upper_parity (d e : ComplexCharacterData) :
    pairParity (P.hi d 0) (P.hi e 0) =
      (((d.weight.natAbs + e.weight.natAbs + 2) % 2 : ℕ) : ℤ) := by
  unfold pairParity RealInducedPairQuotientPresentation.hi
  dsimp [RealJacquetFrobenius.charData]
  omega

/-- The incoming ascending word at a positive canonical linked resonance. -/
theorem exists_ascendingData (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))
    (hH : 0 < innerWeight d e k) :
    ∃ μ₀ μ₂ : ℤ → ℂ,
      RealInducedPairAscendingExchange.MultiplierData e d 0 0
        (binomialMultiplier (outerWeight d e k) (pairParity (P.lo d 0) (P.hi e 0)))
        μ₀ μ₂
        (binomialMultiplier (innerWeight d e k).toNat (pairParity (P.hi d 0) (P.lo e 0))) ∧
      (∀ j, Even (j - pairParity (P.lo d 0) (P.lo e 0)) → μ₀ j ≠ 0) ∧
      (∀ j, Even (j - pairParity (P.hi d 0) (P.hi e 0)) → μ₂ j ≠ 0) := by
  have hsum := RealInducedPairLinkedIncoming.weight_sum d e k
  have hcast : ((innerWeight d e k).toNat : ℤ) = innerWeight d e k :=
    Int.toNat_of_nonneg (by omega)
  have hcc : ((innerWeight d e k).toNat : ℂ) = (innerWeight d e k : ℂ) := by
    exact_mod_cast hcast
  have hP := RealInducedPairOuterTail.outerWeight_pos d e k
  have hHn : 0 < (innerWeight d e k).toNat := by omega
  have hpar1 : Even ((outerWeight d e k : ℤ) - 1 -
      pairParity (P.lo d 0) (P.hi e 0)) := by
    simp only [pairParity, RealInducedPairQuotientPresentation.lo,
      RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData,
      Fin.val_zero, zero_add, Nat.mod_mod]
    rw [Int.even_iff] at hp ⊢
    omega
  have hpar3 : Even (((innerWeight d e k).toNat : ℤ) - 1 -
      pairParity (P.hi d 0) (P.lo e 0)) := by
    simp only [pairParity, RealInducedPairQuotientPresentation.lo,
      RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData,
      Fin.val_zero, zero_add, add_zero, Nat.mod_mod]
    rw [Int.even_iff] at hp ⊢
    omega
  have hp0 : Even (innerWeight d e k + (d.weight.natAbs : ℤ) - (0 : ℤ)) := by
    rw [Int.even_iff] at hp ⊢
    omega
  let ε₂ : ℕ := (d.weight.natAbs + e.weight.natAbs + 2) % 2
  have hp2 : Even (innerWeight d e k + (e.weight.natAbs : ℤ) - (ε₂ : ℤ)) := by
    dsimp [ε₂]
    rw [Int.even_iff] at hp ⊢
    omega
  obtain ⟨μ₀, hr0, hs0, hn0⟩ := RealInducedPairGenericSwap.exists_multiplier 0
    (RealInducedPairLinkedIncoming.isGenericParameter_int 0 hp0)
  obtain ⟨μ₂, hr2, hs2, hn2⟩ := RealInducedPairGenericSwap.exists_multiplier ε₂
    (RealInducedPairLinkedIncoming.isGenericParameter_int ε₂ hp2)
  obtain ⟨hν1, hν0, hν2, hν3⟩ := differences h
  refine ⟨μ₀, μ₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact isSymmetric_binomialMultiplier _ (pairParity_eq _ _)
  · simpa only [sigma0, Int.natAbs_zero, Int.natCast_zero, show pairParity (P.lo d 0) (P.lo e 0) = 0 from rfl] using hs0
  · simpa only [sigma0, upper_parity, Int.natAbs_natCast] using hs2
  · exact isSymmetric_binomialMultiplier _ (pairParity_eq _ _)
  · rw [hν1]
    exact isRecurrent_binomialMultiplier hP (pairParity_eq _ _) hpar1
  · rw [hν0]
    simpa only [Int.cast_add, Int.cast_natCast, Int.natCast_zero,
      show pairParity (P.lo d 0) (P.lo e 0) = 0 from rfl] using hr0
  · rw [hν2, upper_parity]
    simpa only [Int.cast_add, Int.cast_natCast] using hr2
  · rw [hν3, ← hcc]
    exact isRecurrent_binomialMultiplier hHn (pairParity_eq _ _) hpar3
  · simpa only [Int.natCast_zero, show pairParity (P.lo d 0) (P.lo e 0) = 0 from rfl] using hn0
  · simpa only [upper_parity] using hn2

end Parameters

section Application

variable {d e : ComplexCharacterData} {k : ℕ}

abbrev outerPiece (d e : ComplexCharacterData) (k : ℕ) : List RealBlock :=
  [.character (P.lo e 0),
    .induced (pairInduced (P.lo d 0) (P.hi e 0) (outerWeight d e k)),
    .character (P.hi d 0)]

abbrev innerPiece (d e : ComplexCharacterData) (k : ℕ) : List RealBlock :=
  [.character (P.lo d 0),
    .induced (pairInduced (P.hi d 0) (P.lo e 0) (innerWeight d e k).toNat),
    .character (P.hi e 0)]

/-- Canonical parity of the outer crossing. -/
theorem outer_parity (d e : ComplexCharacterData) (k : ℕ)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ))) :
    Even ((outerWeight d e k : ℤ) - 1 - pairParity (P.lo d 0) (P.hi e 0)) := by
  simp only [pairParity, RealInducedPairQuotientPresentation.lo,
    RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData,
    Fin.val_zero, zero_add, Nat.mod_mod]
  rw [Int.even_iff] at hp ⊢
  omega

/-- Canonical parity of the positive inner crossing. -/
theorem inner_parity (d e : ComplexCharacterData) (k : ℕ)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))
    (hH : 0 < innerWeight d e k) :
    Even (((innerWeight d e k).toNat : ℤ) - 1 -
      pairParity (P.hi d 0) (P.lo e 0)) := by
  have hsum := RealInducedPairLinkedIncoming.weight_sum d e k
  have hcast : ((innerWeight d e k).toNat : ℤ) = innerWeight d e k :=
    Int.toNat_of_nonneg (by omega)
  simp only [pairParity, RealInducedPairQuotientPresentation.lo,
    RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData,
    Fin.val_zero, zero_add, add_zero, Nat.mod_mod]
  rw [Int.even_iff] at hp ⊢
  omega

/-- The natural positive inner weight is the last endpoint difference. -/
theorem inner_difference (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    (P.lo e 0).exponent - (P.hi d 0).exponent = ((innerWeight d e k).toNat : ℂ) := by
  rw [(differences h).2.2.2]
  exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hH)).symm

/-- The binomial at the first crossing. -/
def outerBinomial (d e : ComplexCharacterData) (k : ℕ) :
    KF 4 (P.X e d 0 0) →ₗ[ℂ] KF 4 (X1 e d 0 0) :=
  blockFrobMap (data_q0 (n := 4) (pre := [.character (P.lo e 0)])
    (post := [.character (P.hi d 0)]) (c := P.lo d 0) (d := P.hi e 0)
    (ℓ := outerWeight d e k) rfl)

/-- The binomial at the last crossing. -/
def innerBinomial (d e : ComplexCharacterData) (k : ℕ) :
    KF 4 (X1 d e 0 0) →ₗ[ℂ] KF 4 (P.X d e 0 0) :=
  blockFrobMap (data_q0 (n := 4) (pre := [.character (P.lo d 0)])
    (post := [.character (P.hi e 0)]) (c := P.hi d 0) (d := P.lo e 0)
    (ℓ := (innerWeight d e k).toNat) rfl)

/-- The inverse-tail section of the outer fused block. -/
def outerSection (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ))) :
    KF 4 (outerPiece d e k) →ₗ[ℂ] KF 4 (X1 e d 0 0) :=
  blockFrobMap (data_q1 (n := 4) (pre := [.character (P.lo e 0)])
    (post := [.character (P.hi d 0)]) rfl
    (RealInducedPairOuterTail.outerWeight_pos d e k) (outer_parity d e k hp)
    (differences h).1)

/-- The inverse-tail section of the inner fused block. -/
def innerSection (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))
    (hH : 0 < innerWeight d e k) :
    KF 4 (innerPiece d e k) →ₗ[ℂ] KF 4 (P.X d e 0 0) :=
  blockFrobMap (data_q1 (n := 4) (pre := [.character (P.lo d 0)])
    (post := [.character (P.hi e 0)]) rfl (by omega)
    (inner_parity d e k hp hH) (inner_difference h hH))

/-- The first two-piece decomposition in the incoming ascending word. -/
theorem outer_decomposition (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ))) :
    IsRealIntertwinerModulo 4 (outerPiece d e k) (X1 e d 0 0)
      (LinearMap.range (outerBinomial d e k)) (outerSection h hp) ∧
    ∀ f, ∃ z r, outerBinomial d e k z + outerSection h hp r = f :=
  rankOne (n := 4) (pre := [.character (P.lo e 0)])
    (post := [.character (P.hi d 0)]) rfl
    (RealInducedPairOuterTail.outerWeight_pos d e k) (outer_parity d e k hp)
    (differences h).1

/-- The last two-piece decomposition in the incoming ascending word. -/
theorem inner_decomposition (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))
    (hH : 0 < innerWeight d e k) :
    IsRealIntertwinerModulo 4 (innerPiece d e k) (P.X d e 0 0)
      (LinearMap.range (innerBinomial d e k)) (innerSection h hp hH) ∧
    ∀ f, ∃ z r, innerBinomial d e k z + innerSection h hp hH r = f :=
  rankOne (n := 4) (pre := [.character (P.lo d 0)])
    (post := [.character (P.hi e 0)]) rfl (by omega)
    (inner_parity d e k hp hH) (inner_difference h hH)

/-- The last binomial is an exact intertwiner. -/
theorem innerBinomial_exact (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))
    (hH : 0 < innerWeight d e k) :
    IsRealIntertwinerModulo 4 (X1 d e 0 0) (P.X d e 0 0) ⊥
      (innerBinomial d e k) :=
  RealInducedPairQuotientPresentation.binomial_exact (n := 4)
    (pre := [.character (P.lo d 0)]) (post := [.character (P.hi e 0)]) rfl
    (by omega) (inner_parity d e k hp hH) (inner_difference h hH)

section Middle

variable {μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ}
  (hm : RealInducedPairAscendingExchange.MultiplierData e d 0 0 μ₁ μ₀ μ₂ μ₃)

/-- The two disjoint middle crossings, in their specified order. -/
def middle : KF 4 (X1 e d 0 0) →ₗ[ℂ] KF 4 (X1 d e 0 0) :=
  (blockFrobMap hm.data20).comp (blockFrobMap hm.data0)

theorem middle_exact : IsRealIntertwinerModulo 4 (X1 e d 0 0) (X1 d e 0 0) ⊥
    (middle hm) :=
  modulo_comp_bot
    (swap_exact (n := 4) (pre := [.character (P.lo d 0), .character (P.lo e 0)])
      (post := []) rfl hm.sym2 hm.rec2)
    (swap_exact (n := 4) (pre := [])
      (post := [.character (P.hi e 0), .character (P.hi d 0)]) rfl hm.sym0 hm.rec0)

/-- Invert the two generic middle crossings on the full-character spaces. -/
theorem middle_surjective
    (hn0 : ∀ j, Even (j - pairParity (P.lo d 0) (P.lo e 0)) → μ₀ j ≠ 0)
    (hn2 : ∀ j, Even (j - pairParity (P.hi d 0) (P.hi e 0)) → μ₂ j ≠ 0) :
    Function.Surjective (middle hm) := by
  intro f
  let I₂ := blockFrobMap (data_unswap (n := 4)
    (pre := [.character (P.lo d 0), .character (P.lo e 0)])
    (post := []) rfl hm.sym2)
  let I₀ := blockFrobMap (data_unswap (n := 4) (pre := [])
    (post := [.character (P.hi e 0), .character (P.hi d 0)]) rfl hm.sym0)
  refine ⟨I₀ (I₂ f), ?_⟩
  change blockFrobMap hm.data20 (blockFrobMap hm.data0 (I₀ (I₂ f))) = f
  rw [RealCharacterInducedPushforward.frob_inv_of_ne_zero hm.data0 _ hn0]
  exact RealCharacterInducedPushforward.frob_inv_of_ne_zero hm.data20 _ hn2 f

end Middle

/-- Push a section modulo an image through an exact map. -/
theorem modulo_comp_range {n : ℕ} {a b c z : List RealBlock}
    {B : KF n b →ₗ[ℂ] KF n c} {Q : KF n z →ₗ[ℂ] KF n b}
    {S : KF n a →ₗ[ℂ] KF n b}
    (hB : IsRealIntertwinerModulo n b c ⊥ B)
    (hS : IsRealIntertwinerModulo n a b (LinearMap.range Q) S) :
    IsRealIntertwinerModulo n a c (LinearMap.range (B.comp Q)) (B.comp S) := by
  apply modulo_mono (modulo_comp hB hS)
  rw [bot_sup_eq, ← LinearMap.range_comp]

/-- An onto map carries a two-piece spanning identity to its target. -/
theorem span_comp {n : ℕ} {a b c z : List RealBlock}
    (B : KF n b →ₗ[ℂ] KF n c) (Q : KF n z →ₗ[ℂ] KF n b)
    (S : KF n a →ₗ[ℂ] KF n b)
    (hB : Function.Surjective B) (hspan : ∀ v, ∃ z r, Q z + S r = v) :
    ∀ y, ∃ z r, (B.comp Q) z + (B.comp S) r = y := by
  intro y
  obtain ⟨v, rfl⟩ := hB y
  obtain ⟨z, r, hr⟩ := hspan v
  exact ⟨z, r, by change B (Q z) + B (S r) = B v; rw [← map_add, hr]⟩

section CanonicalWord

variable {μ₀ μ₂ : ℤ → ℂ}
  (hm : RealInducedPairAscendingExchange.MultiplierData e d 0 0
    (binomialMultiplier (outerWeight d e k) (pairParity (P.lo d 0) (P.hi e 0)))
    μ₀ μ₂
    (binomialMultiplier (innerWeight d e k).toNat (pairParity (P.hi d 0) (P.lo e 0))))

theorem first_eq : blockFrobMap hm.data1 = outerBinomial d e k := rfl

theorem last_eq : blockFrobMap hm.data3 = innerBinomial d e k := rfl

/-- The named binomials and middle composite are exactly the four crossings. -/
theorem crossings_eq : hm.crossings =
    (innerBinomial d e k).comp ((middle hm).comp (outerBinomial d e k)) := by
  unfold RealInducedPairAscendingExchange.MultiplierData.crossings
  rw [first_eq hm, last_eq hm]
  exact congrArg (fun F => (innerBinomial d e k).comp F) (LinearMap.comp_assoc _ _ _).symm

/-- The assembled full-character map equals the map which descends. -/
theorem beforeDescent_eq (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) :
    hm.beforeDescent he hd = (P.quotientMap d e 0 0 hd he).comp
      ((innerBinomial d e k).comp ((middle hm).comp (outerBinomial d e k))) :=
  congrArg (fun F => (P.quotientMap d e 0 0 hd he).comp F) (crossings_eq hm)

end CanonicalWord

/-- The actual ascending exchange and the two fused sections span the target. -/
theorem filtration_of_pieces
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))
    (hH : 0 < innerWeight d e k)
    {C : List RealBlock → Prop}
    (hW : C [.induced e, .induced d])
    (hR : C (outerPiece d e k)) (hU : C (innerPiece d e k)) :
    HasFiltration 4 [.induced d, .induced e] C := by
  obtain ⟨μ₀, μ₂, hm, hn0, hn2⟩ := exists_ascendingData h hp hH
  obtain ⟨hq, hfac, hrange⟩ := hm.swap_descend he hd
  apply assemble (P.quotientMap d e 0 0 hd he) (innerBinomial d e k)
    ((middle hm).comp (outerBinomial d e k)) ((middle hm).comp (outerSection h hp))
    (innerSection h hp hH) (hm.swap he hd) (P.quotientMap e d 0 0 he hd)
    (RealInducedPairQuotientPresentation.quotient_exact d e 0 0 hd he)
    (RealInducedPairQuotientPresentation.quotient_surjective d e 0 0 hd he)
    (innerBinomial_exact h hp hH)
    (modulo_comp_range (middle_exact hm) (outer_decomposition h hp).1)
    (inner_decomposition h hp hH).1 hq ?_ ?_
    (span_comp (middle hm) _ _ (middle_surjective hm hn0 hn2) (outer_decomposition h hp).2)
    (inner_decomposition h hp hH).2 hW hR hU
  · exact hfac.trans (beforeDescent_eq hm hd he)
  · exact hrange.trans (congrArg LinearMap.range (beforeDescent_eq hm hd he))

/-- The outer fused block and its remaining characters preserve all four endpoints. -/
theorem outer_support (h : IsLinkedAt d e k) :
    (realExponentSupport (outerPiece d e k)).Perm
      (realExponentSupport [.induced d, .induced e]) := by
  have hs := realExponentSupport_pairInduced_eq (differences h).1
  have hR : realExponentSupport (outerPiece d e k) =
      [(P.lo e 0).exponent, (P.hi e 0).exponent,
        (P.lo d 0).exponent, (P.hi d 0).exponent] := by
    change [(P.lo e 0).exponent] ++
      realExponentSupport [.induced (pairInduced (P.lo d 0) (P.hi e 0) (outerWeight d e k))] ++
      [(P.hi d 0).exponent] = _
    rw [hs]
    rfl
  rw [hR]
  change [(P.lo e 0).exponent, (P.hi e 0).exponent,
    (P.lo d 0).exponent, (P.hi d 0).exponent].Perm
    [(P.hi d 0).exponent, (P.lo d 0).exponent, (P.hi e 0).exponent, (P.lo e 0).exponent]
  exact (List.reverse_perm _).symm

/-- The inner fused block and its remaining characters preserve all four endpoints. -/
theorem inner_support (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    (realExponentSupport (innerPiece d e k)).Perm
      (realExponentSupport [.induced d, .induced e]) := by
  have hs := realExponentSupport_pairInduced_eq (inner_difference h hH)
  have hU : realExponentSupport (innerPiece d e k) =
      [(P.lo d 0).exponent, (P.lo e 0).exponent,
        (P.hi d 0).exponent, (P.hi e 0).exponent] := by
    change [(P.lo d 0).exponent] ++
      realExponentSupport [.induced
        (pairInduced (P.hi d 0) (P.lo e 0) (innerWeight d e k).toNat)] ++
      [(P.hi e 0).exponent] = _
    rw [hs]
    rfl
  rw [hU]
  change [(P.lo d 0).exponent, (P.lo e 0).exponent,
    (P.hi d 0).exponent, (P.hi e 0).exponent].Perm
    [(P.hi d 0).exponent, (P.lo d 0).exponent, (P.hi e 0).exponent, (P.lo e 0).exponent]
  exact (List.perm_append_comm (l₁ := [(P.lo d 0).exponent, (P.lo e 0).exponent])
    (l₂ := [(P.hi d 0).exponent, (P.hi e 0).exponent])).trans
      ((List.Perm.swap _ _ _).cons _)

@[simp] theorem outer_weightSquareSum (d e : ComplexCharacterData) (k : ℕ) :
    realWeightSquareSum (outerPiece d e k) = outerWeight d e k ^ 2 := by
  simp [outerPiece, realWeightSquareSum, realBlockWeightSquare]

@[simp] theorem inner_weightSquareSum (d e : ComplexCharacterData) (k : ℕ) :
    realWeightSquareSum (innerPiece d e k) = (innerWeight d e k).toNat ^ 2 := by
  simp only [innerPiece, realWeightSquareSum, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, realBlockWeightSquare, pairInduced_weight,
    Int.natAbs_natCast, zero_add, add_zero]

/-- When even the inner fused piece is heavier, the three pieces are allowed. -/
theorem filtration (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))
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
  apply filtration_of_pieces hd he h hp hH
  · exact ⟨[.induced e, .induced d], rfl, Or.inl rfl⟩
  · refine ⟨outerPiece d e k, rfl, Or.inr ⟨outer_support h, ?_⟩⟩
    rw [outer_weightSquareSum]
    simpa [realWeightSquareSum, realBlockWeightSquare] using hP
  · refine ⟨innerPiece d e k, rfl, Or.inr ⟨inner_support h hH, ?_⟩⟩
    rw [inner_weightSquareSum]
    simpa [realWeightSquareSum, realBlockWeightSquare] using hb

end Application

end RealInducedPairDistantFiltration

open RealInducedPairLinkedReplacement in
/-- The actual two-induced-block filtration at canonical linked resonances where
the positive inner weight alone has larger squared weight than the original pair. -/
def RealInducedPairDistantFiltrationStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ),
    0 < d.weight.natAbs → 0 < e.weight.natAbs → IsLinkedAt d e k →
      Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)) →
        d.weight.natAbs ^ 2 + e.weight.natAbs ^ 2 < (innerWeight d e k).toNat ^ 2 →
          RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)

theorem realInducedPairDistantFiltration : RealInducedPairDistantFiltrationStatement := by
  intro d e k hd he h hp hb
  exact RealInducedPairDistantFiltration.filtration hd he h hp hb

end Langlands.Archimedean
