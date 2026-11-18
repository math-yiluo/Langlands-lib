import Langlands.Representation.Archimedean.RealCompactPolynomialFourierRelation
import Langlands.Representation.Archimedean.RealCharacterPairReducible
import Langlands.Representation.Archimedean.RealCharacterCrossing
import Langlands.Representation.Archimedean.RealTailCompactPolynomialNormalization
import Langlands.Representation.Archimedean.RealCompactPolynomialBraid

/-! # Differential character crossings and their actual parity changes -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealDifferentialCharacterBraid

open RealStandardFiltration RealBlockFrobeniusMap RealBlockMultiplier RealCharacterPair
open RealCharacterPairReducible RealBlockPosition RealBlockJacquet
open Polynomial Complex RealTailMultiplierPolynomial RealCompactPolynomialRelations

def flip (c : RealCharacterData) : RealCharacterData :=
  RealJacquetFrobenius.charData ⟨(c.parity.val + 1) % 2, Nat.mod_lt _ two_pos⟩ c.exponent

@[simp] theorem flip_exponent (c : RealCharacterData) : (flip c).exponent = c.exponent := rfl

@[simp] theorem flip_flip (c : RealCharacterData) : flip (flip c) = c := by
  have hp : (⟨(((c.parity.val + 1) % 2) + 1) % 2, Nat.mod_lt _ two_pos⟩ : Fin 2) = c.parity := by
    apply Fin.ext
    change (((c.parity.val + 1) % 2) + 1) % 2 = c.parity.val
    have hc := c.parity.isLt
    omega
  change RealJacquetFrobenius.charData
    ⟨(((c.parity.val + 1) % 2) + 1) % 2, Nat.mod_lt _ two_pos⟩ c.exponent = c
  rw [hp]
  exact RealCharacterCrossing.charData_eta c

theorem flip_sign (c : RealCharacterData) :
    (-1 : ℂ) ^ (flip c).parity.val = -(-1 : ℂ) ^ c.parity.val := by
  have hc : c.parity.val = 0 ∨ c.parity.val = 1 := by have := c.parity.isLt; omega
  rcases hc with hc | hc <;> norm_num [flip, RealJacquetFrobenius.charData, hc]

theorem differential_sign {c d : RealCharacterData} {ℓ : ℕ}
    (hpar : Even ((ℓ : ℤ) - 1 - pairParity c d)) :
    (-1 : ℂ) ^ ℓ = -sigma0 c d := by
  rw [neg_one_pow_eq_pow_mod_two (n := ℓ)]
  rcases pairParity_eq c d with he | he
  · have hℓ : ℓ % 2 = 1 := by rw [he, Int.even_iff] at hpar; omega
    rw [hℓ, sigma0, he]
    norm_num
  · have hℓ : ℓ % 2 = 0 := by rw [he, Int.even_iff] at hpar; omega
    rw [hℓ, sigma0, he]
    norm_num

section Crossing

variable {n ℓ : ℕ} {pre post : List RealBlock} {c d : RealCharacterData}

/-- A differential tail crossing reverses the pair and flips both character parities. -/
theorem data
    (hn : realRank (pre ++ .character c :: .character d :: post) = n)
    (hℓ : 0 < ℓ) (hpar : Even ((ℓ : ℤ) - 1 - pairParity c d)) :
    IsBlockFrobData n (pre ++ .character c :: .character d :: post)
      (pre ++ .character (flip d) :: .character (flip c) :: post) (realRank pre)
      (pairParity c d) ((-1 : ℂ) ^ ℓ) (tailMultiplier ℓ (pairParity c d) ((-1 : ℂ) ^ ℓ)) := by
  have hn' : realRank (pre ++ [.character (flip d), .character (flip c)] ++ post) = n := by
    simpa only [realRank, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, RealBlock.rank, add_zero, add_assoc] using hn
  rw [← mid_pair pre post (.character c) (.character d),
    ← mid_pair pre post (.character (flip d)) (.character (flip c))]
  refine IsBlockFrobData.of_mid hn' rfl rfl rfl rfl ?_
    (isSymmetric_tailMultiplier hℓ (pairParity_eq c d) hpar (neg_one_pow_sq ℓ)) ?_ ?_ ?_
  · simp only [realPositionCharacter_neg_one, neg_one_pow_pairParity', realPositionSign]
  · simp only [realPositionCharacter_neg_one, realPositionSign]
    rw [flip_sign, differential_sign hpar, sigma0_eq]
    linear_combination ((-1 : ℂ) ^ d.parity.val) * neg_one_pow_sq_fin c.parity
  · simp only [realPositionCharacter_neg_one, realPositionSign]
    rw [flip_sign, differential_sign hpar, sigma0_eq]
    linear_combination ((-1 : ℂ) ^ c.parity.val) * neg_one_pow_sq_fin d.parity
  · intro e he
    simp [realInducedBlockAt] at he

def crossing
    (hn : realRank (pre ++ .character c :: .character d :: post) = n)
    (hℓ : 0 < ℓ) (hpar : Even ((ℓ : ℤ) - 1 - pairParity c d)) :
    KF n (pre ++ .character c :: .character d :: post) →ₗ[ℂ]
      KF n (pre ++ .character (flip d) :: .character (flip c) :: post) :=
  blockFrobMap (data hn hℓ hpar)

theorem crossing_exact
    (hn : realRank (pre ++ .character c :: .character d :: post) = n)
    (hℓ : 0 < ℓ) (hpar : Even ((ℓ : ℤ) - 1 - pairParity c d))
    (hgap : d.exponent - c.exponent = (ℓ : ℂ)) :
    IsRealIntertwinerModulo n (pre ++ .character c :: .character d :: post)
      (pre ++ .character (flip d) :: .character (flip c) :: post) ⊥
      (crossing hn hℓ hpar) := by
  apply isRealIntertwinerModulo_blockFrobMap
  have h0 : GramFormula.realPositionExponent
      (pre ++ .character c :: .character d :: post) (realRank pre) = c.exponent := by
    rw [← mid_pair pre post (.character c) (.character d),
      exponent_mid_zero pre post (realRank_cd (c := c) (d := d) ▸ two_pos)]
    rfl
  have h1 : GramFormula.realPositionExponent
      (pre ++ .character c :: .character d :: post) (realRank pre + 1) = d.exponent := by
    rw [← mid_pair pre post (.character c) (.character d),
      exponent_mid_one pre post (realRank_cd (c := c) (d := d) ▸ one_lt_two)]
    rfl
  rw [h0, h1, show c.exponent - d.exponent + 1 = 1 - (ℓ : ℂ) by linear_combination -hgap]
  exact isRecurrent_tailMultiplier hℓ (pairParity_eq c d) hpar (neg_one_pow_sq ℓ)

theorem crossing_fourier
    (hn : realRank (pre ++ .character c :: .character d :: post) = n)
    (hℓ : 0 < ℓ) (hpar : Even ((ℓ : ℤ) - 1 - pairParity c d))
    (f : KF n (pre ++ .character c :: .character d :: post))
    (j : ℤ) {g : Langlands.GeneralLinear n ℝ} (hg : g ∈ unitaryCompact ℝ n) :
    blockFourierCoefficient n (realRank pre) j (crossing hn hℓ hpar f) g =
      (RealTailMultiplierPolynomial.tailPolynomial ℓ).eval (j : ℂ) *
        blockFourierCoefficient n (realRank pre) j f g := by
  change blockFourierCoefficient n (realRank pre) j (blockFrobMap (data hn hℓ hpar) f) g = _
  rw [blockFourierCoefficient_blockFrobMap (data hn hℓ hpar) f hg]
  by_cases he : Even (j - pairParity c d)
  · rw [RealTailMultiplierPolynomial.tailPolynomial_eq hℓ (pairParity_eq c d) hpar j he]
  · rw [blockFourierCoefficient_eq_zero_of_not_even
      (data hn hℓ hpar).lt (data hn hℓ hpar).par f he g, mul_zero, mul_zero]

end Crossing

section PolynomialBraid

variable {A : Type*} [Ring A] [Algebra ℂ A] {X Y Z : A}

theorem normalized_braid
    (hXY : X * Y - Y * X = Z) (hZX : Z * X - X * Z = Y)
    (hZY : Z * Y - Y * Z = -X) (n m : ℕ) (hm : m = 1 ∨ m = 2) :
    aeval ((-I : ℂ) • X) (tailPolynomial m) *
        aeval ((-I : ℂ) • Y) (tailPolynomial (n + m)) *
        aeval ((-I : ℂ) • X) (tailPolynomial n) =
      aeval ((-I : ℂ) • Y) (tailPolynomial n) *
        aeval ((-I : ℂ) • X) (tailPolynomial (n + m)) *
        aeval ((-I : ℂ) • Y) (tailPolynomial m) := by
  have hf : factor X m * factor Y (n + m) * factor X n =
      factor Y n * factor X (n + m) * factor Y m := by
    rcases hm with rfl | rfl
    · simpa only [RealCompactPolynomialRelations.factor] using
        RealCompactPolynomialBraid.braid_one_nat hXY hZX hZY n
    · exact RealCompactPolynomialBraid.braid_two_nat hXY hZX hZY n
  simp_rw [RealTailCompactPolynomialNormalization.operator_eq_factor]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hf]
  congr 1
  ring

theorem normalized_braid_small
    (hXY : X * Y - Y * X = Z) (hZX : Z * X - X * Z = Y)
    (hZY : Z * Y - Y * Z = -X) (n m : ℕ)
    (hsmall : (n = 1 ∨ n = 2) ∨ (m = 1 ∨ m = 2)) :
    aeval ((-I : ℂ) • X) (tailPolynomial m) *
        aeval ((-I : ℂ) • Y) (tailPolynomial (n + m)) *
        aeval ((-I : ℂ) • X) (tailPolynomial n) =
      aeval ((-I : ℂ) • Y) (tailPolynomial n) *
        aeval ((-I : ℂ) • X) (tailPolynomial (n + m)) *
        aeval ((-I : ℂ) • Y) (tailPolynomial m) := by
  rcases hsmall with hn | hm
  · have hYX : Y * X - X * Y = -Z := by
      linear_combination (norm := noncomm_ring) -hXY
    have hZY' : (-Z) * Y - Y * (-Z) = X := by
      linear_combination (norm := noncomm_ring) -hZY
    have hZX' : (-Z) * X - X * (-Z) = -Y := by
      linear_combination (norm := noncomm_ring) -hZX
    simpa only [Nat.add_comm] using (normalized_braid hYX hZY' hZX' m n hn).symm
  · exact normalized_braid hXY hZX hZY n m hm

end PolynomialBraid

namespace Word

def before : Fin 6 → Fin 7 := ![0, 1, 2, 0, 4, 5]
def after : Fin 6 → Fin 7 := ![1, 2, 3, 4, 5, 6]
def position : Fin 6 → ℕ := ![0, 1, 0, 1, 0, 1]
def cutoff (n m : ℕ) : Fin 6 → ℕ := ![n, n + m, m, m, n + m, n]

theorem position_lt (s : Fin 6) : position s + 1 < 3 := by
  fin_cases s <;> decide

end Word

open RealKTypeCount RealOrthogonalUncertainty RealCompactPolynomialFourierRelation in
/-- The abstract polynomial braid compares actual compact-finite Fourier multiplier words. -/
theorem functional_braid (n m : ℕ)
    (hsmall : (n = 1 ∨ n = 2) ∨ (m = 1 ∨ m = 2))
    (fs : Fin 7 → Langlands.GeneralLinear 3 ℝ → ℂ)
    (hc : ∀ i, Continuous (fs i))
    (hK : ∀ i, fs i ∈ kFiniteVectors
      (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ)) (unitaryCompact ℝ 3))
    (hstep : ∀ s : Fin 6, ∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 (Word.position s) j (fs (Word.after s)) x =
        (tailPolynomial (Word.cutoff n m s)).eval (j : ℂ) *
          blockFourierCoefficient 3 (Word.position s) j (fs (Word.before s)) x) :
    ∀ x ∈ unitaryCompact ℝ 3, fs 3 x = fs 6 x := by
  obtain ⟨N, hN⟩ := exists_common_degree fs hc hK
  let v (i : Fin 7) : degreeLE 3 N := vector (fs i) (hN i)
  have hs : ∀ s : Fin 6,
      v (Word.after s) =
        aeval (-I • gen N (Word.position_lt s)) (tailPolynomial (Word.cutoff n m s))
          (v (Word.before s)) := by
    intro s
    have hh := (relation_iff (Word.position_lt s) (fs (Word.after s)) (fs (Word.before s))
      (hN (Word.after s)) (hN (Word.before s)) 1 (tailPolynomial (Word.cutoff n m s))).mp
        (fun j x hx => by simpa only [eval_one, one_mul] using hstep s j x hx)
    simpa only [map_one, Module.End.one_apply] using hh
  have hp0 : 0 + 1 < 3 := by decide
  have hp1 : 1 + 1 < 3 := by decide
  obtain ⟨z, hXY, hYZ, hZX⟩ := exists_relations N (Or.inl ⟨rfl, rfl⟩) hp0 hp1
  have hZY : z * gen N hp1 - gen N hp1 * z = -gen N hp0 := by
    apply LinearMap.ext
    intro w
    have hh := LinearMap.congr_fun hYZ w
    change gen N hp1 (z w) - z (gen N hp1 w) = gen N hp0 w at hh
    change z (gen N hp1 w) - gen N hp1 (z w) = -(gen N hp0 w)
    rw [← hh]
    abel
  have hB := normalized_braid_small (X := gen N hp0) (Y := gen N hp1) (Z := z)
    hXY hZX hZY n m hsmall
  have h01 := hs 0
  have h12 := hs 1
  have h23 := hs 2
  have h04 := hs 3
  have h45 := hs 4
  have h56 := hs 5
  change v 1 = aeval (-I • gen N hp0) (tailPolynomial n) (v 0) at h01
  change v 2 = aeval (-I • gen N hp1) (tailPolynomial (n + m)) (v 1) at h12
  change v 3 = aeval (-I • gen N hp0) (tailPolynomial m) (v 2) at h23
  change v 4 = aeval (-I • gen N hp1) (tailPolynomial m) (v 0) at h04
  change v 5 = aeval (-I • gen N hp0) (tailPolynomial (n + m)) (v 4) at h45
  change v 6 = aeval (-I • gen N hp1) (tailPolynomial n) (v 5) at h56
  have hv : v 3 = v 6 := by
    rw [h23, h12, h01, h56, h45, h04]
    simpa only [Module.End.mul_apply] using LinearMap.congr_fun hB (v 0)
  intro x hx
  let κ : Matrix.unitaryGroup (Fin 3) ℝ := ⟨(x : Matrix (Fin 3) (Fin 3) ℝ), hx⟩
  have hh := congrFun (congrArg Subtype.val hv) κ
  change fs 3 (Unitary.toUnits κ) = fs 6 (Unitary.toUnits κ) at hh
  simpa only [κ, RealKTypeCount.toUnits_mk hx] using hh

open RealOrthogonalBlock in
/-- The compact multiplier-word comparison transfers to every ambient three-coordinate block. -/
theorem ambient_functional_braid {r a : ℕ} (ha : a + 3 ≤ r) (n m : ℕ)
    (hsmall : (n = 1 ∨ n = 2) ∨ (m = 1 ∨ m = 2))
    (fs : Fin 7 → Langlands.GeneralLinear r ℝ → ℂ)
    (hc : ∀ i, Continuous (fs i))
    (hK : ∀ i, fs i ∈ kFiniteVectors
      (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear r ℝ)) (unitaryCompact ℝ r))
    (hstep : ∀ s : Fin 6, ∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ r,
      blockFourierCoefficient r (a + Word.position s) j (fs (Word.after s)) x =
        (tailPolynomial (Word.cutoff n m s)).eval (j : ℂ) *
          blockFourierCoefficient r (a + Word.position s) j (fs (Word.before s)) x) :
    ∀ x ∈ unitaryCompact ℝ r, fs 3 x = fs 6 x := by
  intro x hx
  have hlocal := functional_braid n m hsmall (fun i => restrictCoset a ha x (fs i))
    (fun i => continuous_restrictCoset a ha x (hc i))
    (fun i => restrictCoset_mem_kFiniteVectors a ha hx (hK i))
    (fun s j k hk => by
      rw [blockFourierCoefficient_restrictCoset a ha (Word.position_lt s),
        blockFourierCoefficient_restrictCoset a ha (Word.position_lt s)]
      exact hstep s j _ ((unitaryCompact ℝ r).mul_mem (block_mem_unitaryCompact a ha hk) hx))
  have hz := hlocal 1 (one_mem _)
  change fs 3 (block a ha 1 * x) = fs 6 (block a ha 1 * x) at hz
  simpa only [map_one, one_mul] using hz

section ActualWords

structure Parameters (a b c : RealCharacterData) (n m : ℕ) : Prop where
  pos0 : 0 < n
  pos1 : 0 < m
  parity0 : Even ((n : ℤ) - 1 - pairParity a b)
  parity1 : Even ((m : ℤ) - 1 - pairParity b c)
  gap0 : b.exponent - a.exponent = (n : ℂ)
  gap1 : c.exponent - b.exponent = (m : ℂ)

variable {a b c : RealCharacterData} {n m : ℕ}

theorem pairParity_flip_both (a b : RealCharacterData) :
    pairParity (flip a) (flip b) = pairParity a b := by
  dsimp [pairParity, flip, RealJacquetFrobenius.charData]
  omega

theorem middle_left_parity (p : Parameters a b c n m) :
    Even (((n + m : ℕ) : ℤ) - 1 - pairParity (flip a) c) := by
  have h0 := p.parity0
  have h1 := p.parity1
  simp only [pairParity, flip, RealJacquetFrobenius.charData] at h0 h1 ⊢
  rw [Int.even_iff] at h0 h1 ⊢
  omega

theorem middle_right_parity (p : Parameters a b c n m) :
    Even (((n + m : ℕ) : ℤ) - 1 - pairParity a (flip c)) := by
  have hp : pairParity a (flip c) = pairParity (flip a) c := by
    dsimp [pairParity, flip, RealJacquetFrobenius.charData]
    omega
  rw [hp]
  exact middle_left_parity p

abbrev source (a b c : RealCharacterData) : List RealBlock :=
  [.character a, .character b, .character c]

abbrev rawTarget (a b c : RealCharacterData) : List RealBlock :=
  [.character (flip (flip c)), .character (flip (flip b)), .character (flip (flip a))]

theorem rawTarget_eq (a b c : RealCharacterData) :
    rawTarget a b c = [.character c, .character b, .character a] := by
  simp only [rawTarget, flip_flip]

abbrev leftFirstData (p : Parameters a b c n m) :=
  data (n := 3) (pre := []) (post := [.character c]) (c := a) (d := b)
    rfl p.pos0 p.parity0

abbrev leftMiddleData (p : Parameters a b c n m) :=
  data (n := 3) (pre := [.character (flip b)]) (post := []) (c := flip a) (d := c)
    rfl (by have := p.pos0; omega : 0 < n + m) (middle_left_parity p)

abbrev leftLastData (p : Parameters a b c n m) :=
  data (n := 3) (pre := []) (post := [.character (flip (flip a))])
    (c := flip b) (d := flip c) (ℓ := m)
    rfl p.pos1 (by rw [pairParity_flip_both]; exact p.parity1)

abbrev rightFirstData (p : Parameters a b c n m) :=
  data (n := 3) (pre := [.character a]) (post := []) (c := b) (d := c)
    rfl p.pos1 p.parity1

abbrev rightMiddleData (p : Parameters a b c n m) :=
  data (n := 3) (pre := []) (post := [.character (flip b)]) (c := a) (d := flip c)
    rfl (by have := p.pos0; omega : 0 < n + m) (middle_right_parity p)

abbrev rightLastData (p : Parameters a b c n m) :=
  data (n := 3) (pre := [.character (flip (flip c))]) (post := [])
    (c := flip a) (d := flip b) (ℓ := n)
    rfl p.pos0 (by rw [pairParity_flip_both]; exact p.parity0)

def leftRaw (p : Parameters a b c n m) :
    KF 3 (source a b c) →ₗ[ℂ] KF 3 (rawTarget a b c) :=
  (blockFrobMap (leftLastData p)).comp
    ((blockFrobMap (leftMiddleData p)).comp (blockFrobMap (leftFirstData p)))

def rightRaw (p : Parameters a b c n m) :
    KF 3 (source a b c) →ₗ[ℂ] KF 3 (rawTarget a b c) :=
  (blockFrobMap (rightLastData p)).comp
    ((blockFrobMap (rightMiddleData p)).comp (blockFrobMap (rightFirstData p)))

theorem gap_middle (p : Parameters a b c n m) :
    c.exponent - a.exponent = ((n + m : ℕ) : ℂ) := by
  rw [Nat.cast_add]
  linear_combination p.gap0 + p.gap1

theorem leftRaw_exact (p : Parameters a b c n m) :
    IsRealIntertwinerModulo 3 (source a b c) (rawTarget a b c) ⊥ (leftRaw p) :=
  modulo_comp_bot
    (crossing_exact (n := 3) (pre := []) (post := [.character (flip (flip a))])
      rfl p.pos1 (by rw [pairParity_flip_both]; exact p.parity1)
      (by simpa only [flip_exponent] using p.gap1))
    (modulo_comp_bot
      (crossing_exact (n := 3) (pre := [.character (flip b)]) (post := [])
        rfl (by have := p.pos0; omega : 0 < n + m) (middle_left_parity p)
        (by simpa only [flip_exponent] using gap_middle p))
      (crossing_exact (n := 3) (pre := []) (post := [.character c])
        rfl p.pos0 p.parity0 p.gap0))

theorem rightRaw_exact (p : Parameters a b c n m) :
    IsRealIntertwinerModulo 3 (source a b c) (rawTarget a b c) ⊥ (rightRaw p) :=
  modulo_comp_bot
    (crossing_exact (n := 3) (pre := [.character (flip (flip c))]) (post := [])
      rfl p.pos0 (by rw [pairParity_flip_both]; exact p.parity0)
      (by simpa only [flip_exponent] using p.gap0))
    (modulo_comp_bot
      (crossing_exact (n := 3) (pre := []) (post := [.character (flip b)])
        rfl (by have := p.pos0; omega : 0 < n + m) (middle_right_parity p)
        (by simpa only [flip_exponent] using gap_middle p))
      (crossing_exact (n := 3) (pre := [.character a]) (post := [])
        rfl p.pos1 p.parity1 p.gap1))

theorem raw_braid (p : Parameters a b c n m)
    (hsmall : (n = 1 ∨ n = 2) ∨ (m = 1 ∨ m = 2)) :
    leftRaw p = rightRaw p := by
  apply LinearMap.ext
  intro f
  let f1 := blockFrobMap (leftFirstData p) f
  let f2 := blockFrobMap (leftMiddleData p) f1
  let f3 := blockFrobMap (leftLastData p) f2
  let g1 := blockFrobMap (rightFirstData p) f
  let g2 := blockFrobMap (rightMiddleData p) g1
  let g3 := blockFrobMap (rightLastData p) g2
  let fs : Fin 7 → Langlands.GeneralLinear 3 ℝ → ℂ :=
    ![(f : Langlands.GeneralLinear 3 ℝ → ℂ), f1, f2, f3, g1, g2, g3]
  have hc : ∀ i, Continuous (fs i) := by
    intro i
    fin_cases i <;> exact continuous_coe _
  have hK : ∀ i, fs i ∈ kFiniteVectors
      (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ)) (unitaryCompact ℝ 3) := by
    intro i
    fin_cases i
    · exact f.2.2
    · exact f1.2.2
    · exact f2.2.2
    · exact f3.2.2
    · exact g1.2.2
    · exact g2.2.2
    · exact g3.2.2
  have hnm : 0 < n + m := by have := p.pos0; omega
  have hstep : ∀ s : Fin 6, ∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 (Word.position s) j (fs (Word.after s)) x =
        (tailPolynomial (Word.cutoff n m s)).eval (j : ℂ) *
          blockFourierCoefficient 3 (Word.position s) j (fs (Word.before s)) x := by
    intro s j x hx
    fin_cases s
    · exact crossing_fourier (n := 3) (pre := []) (post := [.character c])
        rfl p.pos0 p.parity0 f j hx
    · exact crossing_fourier (n := 3) (pre := [.character (flip b)]) (post := [])
        rfl hnm (middle_left_parity p) f1 j hx
    · exact crossing_fourier (n := 3) (pre := []) (post := [.character (flip (flip a))])
        rfl p.pos1 (by rw [pairParity_flip_both]; exact p.parity1) f2 j hx
    · exact crossing_fourier (n := 3) (pre := [.character a]) (post := [])
        rfl p.pos1 p.parity1 f j hx
    · exact crossing_fourier (n := 3) (pre := []) (post := [.character (flip b)])
        rfl hnm (middle_right_parity p) g1 j hx
    · exact crossing_fourier (n := 3) (pre := [.character (flip (flip c))]) (post := [])
        rfl p.pos0 (by rw [pairParity_flip_both]; exact p.parity0) g2 j hx
  have heq := functional_braid n m hsmall fs hc hK hstep
  change f3 = g3
  apply Subtype.ext
  exact eq_of_eqOn_unitaryCompact_of_mem_principalSeries f3.2.1.1 g3.2.1.1 heq

def leftWord (p : Parameters a b c n m) :
    KF 3 (source a b c) →ₗ[ℂ] KF 3 [.character c, .character b, .character a] :=
  (ofEqMap (congrArg (KF 3) (rawTarget_eq a b c))).comp (leftRaw p)

def rightWord (p : Parameters a b c n m) :
    KF 3 (source a b c) →ₗ[ℂ] KF 3 [.character c, .character b, .character a] :=
  (ofEqMap (congrArg (KF 3) (rawTarget_eq a b c))).comp (rightRaw p)

/-- The actual differential character braid, when either adjacent gap is one or two. -/
theorem braid (p : Parameters a b c n m)
    (hsmall : (n = 1 ∨ n = 2) ∨ (m = 1 ∨ m = 2)) :
    leftWord p = rightWord p :=
  congrArg (fun T => (ofEqMap (congrArg (KF 3) (rawTarget_eq a b c))).comp T)
    (raw_braid p hsmall)

theorem leftWord_exact (p : Parameters a b c n m) :
    IsRealIntertwinerModulo 3 (source a b c) [.character c, .character b, .character a] ⊥
      (leftWord p) :=
  modulo_comp_bot (modulo_ofEqMap _) (leftRaw_exact p)

theorem rightWord_exact (p : Parameters a b c n m) :
    IsRealIntertwinerModulo 3 (source a b c) [.character c, .character b, .character a] ⊥
      (rightWord p) :=
  modulo_comp_bot (modulo_ofEqMap _) (rightRaw_exact p)

end ActualWords

end RealDifferentialCharacterBraid

open RealStandardFiltration RealDifferentialCharacterBraid in
/-- Equality and exact intertwining of two actual differential three-character words. -/
def RealDifferentialCharacterBraidStatement : Prop :=
  ∀ (a b c : RealCharacterData) (n m : ℕ) (p : Parameters a b c n m),
    ((n = 1 ∨ n = 2) ∨ (m = 1 ∨ m = 2)) →
      leftWord p = rightWord p ∧
      IsRealIntertwinerModulo 3 (source a b c) [.character c, .character b, .character a] ⊥
        (leftWord p) ∧
      IsRealIntertwinerModulo 3 (source a b c) [.character c, .character b, .character a] ⊥
        (rightWord p)

theorem realDifferentialCharacterBraid : RealDifferentialCharacterBraidStatement :=
  fun _ _ _ _ _ p hsmall =>
    ⟨RealDifferentialCharacterBraid.braid p hsmall,
      RealDifferentialCharacterBraid.leftWord_exact p,
      RealDifferentialCharacterBraid.rightWord_exact p⟩

end Langlands.Archimedean
