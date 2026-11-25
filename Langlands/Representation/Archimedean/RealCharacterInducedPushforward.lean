import Langlands.Representation.Archimedean.RealCharacterPairFiltration
import Langlands.Representation.Archimedean.RealSwapFLanding
import Langlands.Representation.Archimedean.RealStandardFiltration

/-!
# The filtration for a character and an induction block by pushforward

Let `c = sgn^ε |·|^s` be a real character and `d` a complex character of weight `m ≠ 0` and
exponent `t`, `ℓ = |m|`, `a = t + ℓ/2`, `b = t - ℓ/2`. Choose a sign `s_b` and put
`s_a = s_b + ℓ + 1 (mod 2)`, `χ_b = sgn^{s_b} |·|^b`, `χ_a = sgn^{s_a} |·|^a`. Then the real
induction `d'` of the pair `χ_b, χ_a` (`pairInduced`) has the same standard modules as `d`.
This file constructs the filtration of the `O(3)`-finite functions of the standard module of
`[c, d]` by pushing forward filtrations of the principal series `[c, χ_b, χ_a]` along the
tail map `D₁ : K(c, χ_b, χ_a) → K(c, d')`, in two cases for `w = b - s`:

* `w` is not a nonzero integer: the filtration has the single piece `[d, c]`;
* `w` is a positive integer: the pieces are `[d, c]` and `[χ_b, induced(c, χ_a)]`.

The piece `[d, c]` comes from the composite `D₁ ∘ Q₁ ∘ Q₂ : K(χ_b, χ_a, c) → K(c, d')` of
two swaps, which kills the kernel of the tail map `T₀ : K(χ_b, χ_a, c) → K(d', c)`
(`kernel_step`, from `RealSwapFLanding.highModes_eq_zero` and the landing statement), and
hence descends to `K(d', c)`.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealCharacterInducedPushforward

open RealBlockFrobeniusMap RealBlockPosition RealBlockMultiplier RealCharacterPair
open RealCharacterPairReducible RealBlockJacquet RealStandardFiltration GramFormula
open Langlands.LocalFactor.Archimedean

/-! ## Parity bookkeeping -/

/-- The element `k mod 2` of `Fin 2`. -/
def fin2 (k : ℕ) : Fin 2 := ⟨k % 2, Nat.mod_lt _ two_pos⟩

@[simp]
theorem fin2_val (k : ℕ) : (fin2 k).val = k % 2 := rfl

theorem neg_one_pow_congr {k m : ℕ} (h : k % 2 = m % 2) : (-1 : ℂ) ^ k = (-1) ^ m := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

theorem neg_one_pow_eq_mul {k m e : ℕ} (h : k % 2 = (m + e) % 2) :
    (-1 : ℂ) ^ k = (-1) ^ m * (-1) ^ e := by
  rw [← pow_add]
  exact neg_one_pow_congr h

/-- The recurrence on a parity class depends only on the class. -/
theorem isRecurrent_of_even {δ : ℂ} {ε ε' : ℤ} {μ : ℤ → ℂ} (h : IsRecurrent δ ε μ)
    (he : Even (ε - ε')) : IsRecurrent δ ε' μ := fun k hk =>
  h k (by
    obtain ⟨r, hr⟩ := hk
    obtain ⟨s, hs⟩ := he
    exact ⟨r - s, by omega⟩)

/-- The symmetry on a parity class depends only on the class. -/
theorem isSymmetric_of_even {ε ε' : ℤ} {σ σ' : ℂ} {μ : ℤ → ℂ} (h : IsSymmetric ε σ μ)
    (he : Even (ε - ε')) (hσ : σ = σ') : IsSymmetric ε' σ' μ := fun k hk => by
  rw [← hσ]
  exact h k (by
    obtain ⟨r, hr⟩ := hk
    obtain ⟨s, hs⟩ := he
    exact ⟨r - s, by omega⟩)

theorem pairParity_nonneg (c d : RealCharacterData) : 0 ≤ pairParity c d := by
  rcases pairParity_eq c d with h | h <;> omega

/-- A complex number that equals an integer only if the integer is `0` differs from every
nonzero integer. -/
theorem ne_intCast_of {w : ℂ} (hw : ∀ k : ℤ, w = k → k = 0) {q : ℤ} (hq : q ≠ 0) :
    w ≠ q := fun h => hq (hw q h)

/-! ## The generic multiplier without a positivity assumption -/

theorem genericSeq_succ' {ν : ℂ} {ε : ℤ} (hd : ∀ i : ℕ, (ε : ℂ) + 2 * i + 1 + ν ≠ 0)
    (m : ℕ) :
    genericSeq ν ε (m + 1) * (ν + 1 + ε + 2 * m) =
      ((ε : ℂ) + 2 * m + 2 - (ν + 1)) * genericSeq ν ε m := by
  have hd := hd m
  rw [genericSeq, Finset.prod_range_succ, ← genericSeq]
  field_simp
  ring

/-- The generic multiplier solves the recurrence for `δ = ν + 1` whenever its denominators
`ε + 2i + 1 + ν` do not vanish. -/
theorem isRecurrent_genericMultiplier' {ν : ℂ} {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (hd : ∀ i : ℕ, (ε : ℂ) + 2 * i + 1 + ν ≠ 0) :
    IsRecurrent (ν + 1) ε (genericMultiplier ν ε) :=
  isRecurrent_extend hε (neg_one_pow_sq _) (Or.inr rfl) fun m => by
    have := genericSeq_succ' hd m
    linear_combination this

/-- The generic multiplier has no zeros when its numerators and denominators do not
vanish. -/
theorem genericMultiplier_ne_zero' {ν : ℂ} {ε : ℤ}
    (hd : ∀ i : ℕ, (ε : ℂ) + 2 * i + 1 + ν ≠ 0)
    (hne : ∀ m : ℕ, ν ≠ (ε : ℂ) + 2 * m + 1) (k : ℤ) : genericMultiplier ν ε k ≠ 0 := by
  refine (extend_ne_zero_iff (pow_ne_zero _ (by norm_num)) k).mpr ?_
  rw [genericSeq, Finset.prod_ne_zero_iff]
  intro i _
  exact div_ne_zero (sub_ne_zero.mpr (hne i).symm) (hd i)

/-! ## Frobenius maps -/

section Frobenius

variable {n : ℕ} {ds es fs : List RealBlock} {p : ℕ} {ε : ℤ}

/-- A Frobenius map whose multiplier has no zeros on the parity class is onto: the map with
the inverse multiplier is a right inverse. -/
theorem frob_inv_of_ne_zero {σ σ' : ℂ} {μ : ℤ → ℂ} (h : IsBlockFrobData n ds es p ε σ μ)
    (h' : IsBlockFrobData n es ds p ε σ' fun k => (μ k)⁻¹)
    (h0 : ∀ k : ℤ, Even (k - ε) → μ k ≠ 0)
    (g : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)) :
    blockFrobMap h (blockFrobMap h' g) = g :=
  blockFrobMap_blockFrobMap_eq h' h g fun j hj hj1 _ _ =>
    absurd (mul_inv_cancel₀ (h0 j hj)) hj1

/-- The tail map `D` (multiplier `tailMultiplier ℓ ε σ`) into a list with an induction block
of weight `ℓ` at `p` is a left inverse of the map with the inverse tail multiplier. -/
theorem tail_inv {ℓ : ℕ} (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1) (hpar : Even ((ℓ : ℤ) - 1 - ε))
    {σ σ' : ℂ} (hσ : σ ^ 2 = 1)
    (hD : IsBlockFrobData n ds es p ε σ (tailMultiplier ℓ ε σ))
    (hq : IsBlockFrobData n es ds p ε σ' fun k => (tailMultiplier ℓ ε σ k)⁻¹)
    {dI : ComplexCharacterData} (hind : realInducedBlockAt es p = some dI)
    (hw : |dI.weight| = ℓ)
    (f : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)) :
    blockFrobMap hD (blockFrobMap hq f) = f := by
  refine blockFrobMap_blockFrobMap_eq hq hD f fun j hj hne k hk => ?_
  have hP : tailMultiplier ℓ ε σ j = 0 := by
    by_contra hP
    exact hne (mul_inv_cancel₀ hP)
  have hjl : |j| < ℓ := by
    refine abs_lt_of_parity hpar hj (not_lt.mp fun hlt => ?_)
    exact (tailMultiplier_ne_zero_iff hℓ hε hpar hσ hj).mpr hlt hP
  exact f.2.1.2 p dI hind j (by rw [hw]; exact hjl) k

/-- The kernel of the tail map lies in the range of the binomial map. -/
theorem ker_tail_le_range {ℓ : ℕ} (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) {σ σ' τ : ℂ} (hτ : τ ^ 2 = 1)
    (h₀ : IsBlockFrobData n ds es p ε σ (binomialMultiplier ℓ ε))
    (hB : IsBlockFrobData n es ds p ε σ' fun k => (binomialMultiplier ℓ ε k)⁻¹)
    (hD : IsBlockFrobData n es fs p ε τ (tailMultiplier ℓ ε τ)) :
    LinearMap.ker (blockFrobMap hD) ≤ LinearMap.range (blockFrobMap h₀) := by
  refine ker_le_range h₀ hB hD fun j hj hne => ?_
  have hb : binomialMultiplier ℓ ε j = 0 := by
    by_contra hb
    exact hne (mul_inv_cancel₀ hb)
  have hjl : ¬ |j| < ℓ := fun hlt => (binomialMultiplier_ne_zero_iff hℓ hε hpar hj).mpr hlt hb
  refine (tailMultiplier_ne_zero_iff hℓ hε hpar hτ hj).mpr ?_
  rcases (not_lt.mp hjl).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd heq.le (not_le.mpr (abs_lt_of_parity hpar hj heq.symm.le))

end Frobenius

/-! ## Filtrations with two pieces -/

/-- A filtration with two pieces: an exact intertwiner `q₀`, an intertwiner `q₁` modulo the
range of `q₀`, whose ranges span. -/
theorem hasFiltration_two {n : ℕ} {ds e₀ e₁ : List RealBlock} {P : List RealBlock → Prop}
    (h₀ : P e₀) (h₁ : P e₁) (q₀ : KF n e₀ →ₗ[ℂ] KF n ds) (q₁ : KF n e₁ →ₗ[ℂ] KF n ds)
    (hq₀ : IsRealIntertwinerModulo n e₀ ds ⊥ q₀)
    (hq₁ : IsRealIntertwinerModulo n e₁ ds (LinearMap.range q₀) q₁)
    (hspan : ∀ g, ∃ a b, q₀ a + q₁ b = g) : HasFiltration n ds P := by
  let es : Fin 2 → List RealBlock := ![e₀, e₁]
  let q : ∀ j : Fin 2, KF n (es j) →ₗ[ℂ] KF n ds :=
    Fin.cons (α := fun j : Fin 2 => KF n (es j) →ₗ[ℂ] KF n ds) q₀ (Fin.cons q₁ finZeroElim)
  refine ⟨Fin 2, inferInstance, inferInstance, es, q, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact h₀
    · exact h₁
  · intro j
    fin_cases j
    · exact modulo_mono hq₀ bot_le
    · refine modulo_mono hq₁ ?_
      exact le_iSup₂_of_le (f := fun (i : Fin 2) (_ : i < 1) => LinearMap.range (q i))
        (0 : Fin 2) (by decide) le_rfl
  · refine eq_top_iff.2 fun g _ => ?_
    obtain ⟨a, b, rfl⟩ := hspan g
    exact add_mem (Submodule.mem_iSup_of_mem (0 : Fin 2) ⟨a, rfl⟩)
      (Submodule.mem_iSup_of_mem (1 : Fin 2) ⟨b, rfl⟩)

/-! ## Standard modules with the same data -/

theorem abs_weight_eq {d d' : ComplexCharacterData} (hw : d'.weight.natAbs = d.weight.natAbs) :
    |d'.weight| = |d.weight| := by
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs, hw]

/-- Two lists with the same position characters and induction blocks of the same weights at
the same positions have the same standard module. -/
theorem realStandardModule_congr {N : ℕ} {ds ds' : List RealBlock}
    (hχ : realPositionCharacter ds = realPositionCharacter ds')
    (hind : ∀ (p : ℕ) (d₀ : ComplexCharacterData), realInducedBlockAt ds p = some d₀ →
      ∃ d₁, realInducedBlockAt ds' p = some d₁ ∧ |d₁.weight| = |d₀.weight|)
    (hind' : ∀ (p : ℕ) (d₀ : ComplexCharacterData), realInducedBlockAt ds' p = some d₀ →
      ∃ d₁, realInducedBlockAt ds p = some d₁ ∧ |d₁.weight| = |d₀.weight|) :
    realStandardModule N ds = realStandardModule N ds' := by
  ext f
  rw [mem_realStandardModule_iff, mem_realStandardModule_iff, hχ]
  refine and_congr_right fun _ => ⟨fun h p d₀ hd k hk g => ?_, fun h p d₀ hd k hk g => ?_⟩
  · obtain ⟨d₁, hd₁, hw⟩ := hind' p d₀ hd
    exact h p d₁ hd₁ k (by rw [hw]; exact hk) g
  · obtain ⟨d₁, hd₁, hw⟩ := hind p d₀ hd
    exact h p d₁ hd₁ k (by rw [hw]; exact hk) g

/-- The only induction block of `[d, c]` starts at position `0` and is `d`. -/
theorem realInducedBlockAt_induced_character (c : RealCharacterData) (d : ComplexCharacterData)
    {p : ℕ} {d' : ComplexCharacterData}
    (h : realInducedBlockAt [RealBlock.induced d, RealBlock.character c] p = some d') :
    p = 0 ∧ d' = d := by
  rcases p with _ | _ | _ | p
  · simp only [realInducedBlockAt, Option.some.injEq] at h
    exact ⟨rfl, h.symm⟩
  · simp [realInducedBlockAt] at h
  · simp [realInducedBlockAt] at h
  · simp [realInducedBlockAt] at h

section Congr

variable (c : RealCharacterData) {d d' : ComplexCharacterData}
  (hw : d'.weight.natAbs = d.weight.natAbs) (he : d'.exponent = d.exponent)
include hw he

theorem kf_character_induced_congr :
    KF 3 [RealBlock.character c, RealBlock.induced d'] =
      KF 3 [RealBlock.character c, RealBlock.induced d] := by
  have hχ : realPositionCharacter [RealBlock.character c, RealBlock.induced d'] =
      realPositionCharacter [RealBlock.character c, RealBlock.induced d] := by
    funext i x
    rcases i with _ | _ | _ | i
    · rfl
    · simp only [realPositionCharacter, realInducedFirstCharacter, hw, he]
    · simp only [realPositionCharacter, realInducedSecondCharacter, hw, he]
    · rfl
  refine congrArg (fun M => kFiniteFunctions M (unitaryCompact ℝ 3))
    (realStandardModule_congr hχ ?_ ?_)
  · intro p d₀ hd
    obtain ⟨rfl, rfl⟩ := RealSwapFLanding.realInducedBlockAt_character_induced c d' hd
    exact ⟨d, rfl, abs_weight_eq hw.symm⟩
  · intro p d₀ hd
    obtain ⟨rfl, rfl⟩ := RealSwapFLanding.realInducedBlockAt_character_induced c d hd
    exact ⟨d', rfl, abs_weight_eq hw⟩

theorem kf_induced_character_congr :
    KF 3 [RealBlock.induced d', RealBlock.character c] =
      KF 3 [RealBlock.induced d, RealBlock.character c] := by
  have hχ : realPositionCharacter [RealBlock.induced d', RealBlock.character c] =
      realPositionCharacter [RealBlock.induced d, RealBlock.character c] := by
    funext i x
    rcases i with _ | _ | i
    · simp only [realPositionCharacter, realInducedFirstCharacter, hw, he]
    · simp only [realPositionCharacter, realInducedSecondCharacter, hw, he]
    · rfl
  refine congrArg (fun M => kFiniteFunctions M (unitaryCompact ℝ 3))
    (realStandardModule_congr hχ ?_ ?_)
  · intro p d₀ hd
    obtain ⟨rfl, rfl⟩ := realInducedBlockAt_induced_character c d' hd
    exact ⟨d, rfl, abs_weight_eq hw.symm⟩
  · intro p d₀ hd
    obtain ⟨rfl, rfl⟩ := realInducedBlockAt_induced_character c d hd
    exact ⟨d', rfl, abs_weight_eq hw⟩

end Congr

/-! ## The characters `χ_b`, `χ_a` and the induction block `d'` -/

section Setup

variable (c : RealCharacterData) (d : ComplexCharacterData) (sb : Fin 2)

/-- `χ_b = sgn^{s_b} |·|^{t - ℓ/2}`. -/
def chiB : RealCharacterData :=
  RealJacquetFrobenius.charData sb (d.exponent - (d.weight.natAbs : ℂ) / 2)

/-- `χ_a = sgn^{s_a} |·|^{t + ℓ/2}` with `s_a = s_b + ℓ + 1 (mod 2)`. -/
def chiA : RealCharacterData :=
  RealJacquetFrobenius.charData (fin2 (sb.val + d.weight.natAbs + 1))
    (d.exponent + (d.weight.natAbs : ℂ) / 2)

/-- The real induction `d'` of the pair `χ_b, χ_a`: weight `ℓ`, exponent `t`. -/
abbrev dP : ComplexCharacterData := pairInduced (chiB d sb) (chiA d sb) d.weight.natAbs

theorem chiB_exponent : (chiB d sb).exponent = d.exponent - (d.weight.natAbs : ℂ) / 2 := rfl

theorem chiA_exponent : (chiA d sb).exponent = d.exponent + (d.weight.natAbs : ℂ) / 2 := rfl

theorem chiB_parity : (chiB d sb).parity = sb := rfl

theorem chiA_parity_val : (chiA d sb).parity.val = (sb.val + d.weight.natAbs + 1) % 2 := rfl

theorem chiA_sub_chiB :
    (chiA d sb).exponent - (chiB d sb).exponent = (d.weight.natAbs : ℂ) := by
  rw [chiA_exponent, chiB_exponent]
  ring

theorem even_pairParity_chiB_chiA :
    Even ((d.weight.natAbs : ℤ) - 1 - pairParity (chiB d sb) (chiA d sb)) := by
  unfold pairParity
  rw [chiB_parity, chiA_parity_val, Int.even_iff]
  omega

theorem dP_weight_natAbs : (dP d sb).weight.natAbs = d.weight.natAbs := rfl

theorem dP_abs_weight : |(dP d sb).weight| = (d.weight.natAbs : ℤ) := by
  rw [Int.abs_eq_natAbs, dP_weight_natAbs]

theorem dP_exponent : (dP d sb).exponent = d.exponent := by
  rw [pairInduced_exponent, chiB_exponent, chiA_exponent]
  ring

theorem kf_V : KF 3 [RealBlock.character c, RealBlock.induced (dP d sb)] =
    KF 3 [RealBlock.character c, RealBlock.induced d] :=
  kf_character_induced_congr c (dP_weight_natAbs d sb) (dP_exponent d sb)

theorem kf_W : KF 3 [RealBlock.induced (dP d sb), RealBlock.character c] =
    KF 3 [RealBlock.induced d, RealBlock.character c] :=
  kf_induced_character_congr c (dP_weight_natAbs d sb) (dP_exponent d sb)

end Setup

/-! ## The lists and the Frobenius data -/

section Data

variable (c : RealCharacterData) (d : ComplexCharacterData) (sb : Fin 2)

/-- `X = [c, χ_b, χ_a]`. -/
abbrev lX : List RealBlock :=
  [RealBlock.character c, RealBlock.character (chiB d sb), RealBlock.character (chiA d sb)]

/-- `Y = [χ_b, c, χ_a]`. -/
abbrev lY : List RealBlock :=
  [RealBlock.character (chiB d sb), RealBlock.character c, RealBlock.character (chiA d sb)]

/-- `Z = [χ_b, χ_a, c]`. -/
abbrev lZ : List RealBlock :=
  [RealBlock.character (chiB d sb), RealBlock.character (chiA d sb), RealBlock.character c]

/-- `V = [c, d']`. -/
abbrev lV : List RealBlock := [RealBlock.character c, RealBlock.induced (dP d sb)]

/-- `W = [d', c]`. -/
abbrev lW : List RealBlock := [RealBlock.induced (dP d sb), RealBlock.character c]

/-- `[c, sgn^{s_b} |·|^a, sgn^{s_a} |·|^b]`: the target of the projection onto high modes. -/
abbrev lG : List RealBlock :=
  [RealBlock.character c,
    RealBlock.character (RealJacquetFrobenius.charData (chiB d sb).parity (chiA d sb).exponent),
    RealBlock.character (RealJacquetFrobenius.charData (chiA d sb).parity (chiB d sb).exponent)]

/-- The tail map `D₁ : K(c, χ_b, χ_a) → K(c, d')`. -/
theorem dataD1 (hl : 0 < d.weight.natAbs) :
    IsBlockFrobData 3 (lX c d sb) (lV c d sb) 1 (pairParity (chiB d sb) (chiA d sb))
      ((-1) ^ (chiA d sb).parity.val)
      (tailMultiplier d.weight.natAbs (pairParity (chiB d sb) (chiA d sb))
        ((-1) ^ (chiA d sb).parity.val)) :=
  data_D (pre := [RealBlock.character c]) (post := []) (c := chiB d sb) (d := chiA d sb) rfl hl
    (even_pairParity_chiB_chiA d sb) (chiA_sub_chiB d sb)

/-- The inverse tail map `K(c, d') → K(c, χ_b, χ_a)`. -/
theorem dataS1 (hl : 0 < d.weight.natAbs) :
    IsBlockFrobData 3 (lV c d sb) (lX c d sb) 1 (pairParity (chiB d sb) (chiA d sb))
      ((-1) ^ (chiA d sb).parity.val)⁻¹
      (fun k => (tailMultiplier d.weight.natAbs (pairParity (chiB d sb) (chiA d sb))
        ((-1) ^ (chiA d sb).parity.val) k)⁻¹) :=
  data_q1 (pre := [RealBlock.character c]) (post := []) (c := chiB d sb) (d := chiA d sb) rfl hl
    (even_pairParity_chiB_chiA d sb) (chiA_sub_chiB d sb)

/-- The tail map `T₀ : K(χ_b, χ_a, c) → K(d', c)`. -/
theorem dataT0 (hl : 0 < d.weight.natAbs) :
    IsBlockFrobData 3 (lZ c d sb) (lW c d sb) 0 (pairParity (chiB d sb) (chiA d sb))
      ((-1) ^ (chiA d sb).parity.val)
      (tailMultiplier d.weight.natAbs (pairParity (chiB d sb) (chiA d sb))
        ((-1) ^ (chiA d sb).parity.val)) :=
  data_D (pre := []) (post := [RealBlock.character c]) (c := chiB d sb) (d := chiA d sb) rfl hl
    (even_pairParity_chiB_chiA d sb) (chiA_sub_chiB d sb)

/-- The inverse tail map `S₀ : K(d', c) → K(χ_b, χ_a, c)`. -/
theorem dataS0 (hl : 0 < d.weight.natAbs) :
    IsBlockFrobData 3 (lW c d sb) (lZ c d sb) 0 (pairParity (chiB d sb) (chiA d sb))
      ((-1) ^ (chiA d sb).parity.val)⁻¹
      (fun k => (tailMultiplier d.weight.natAbs (pairParity (chiB d sb) (chiA d sb))
        ((-1) ^ (chiA d sb).parity.val) k)⁻¹) :=
  data_q1 (pre := []) (post := [RealBlock.character c]) (c := chiB d sb) (d := chiA d sb) rfl hl
    (even_pairParity_chiB_chiA d sb) (chiA_sub_chiB d sb)

/-- The swap `Q₁ : K(χ_b, c, χ_a) → K(c, χ_b, χ_a)` along the first block. -/
theorem dataQ1 {μ : ℤ → ℂ}
    (hs : IsSymmetric (pairParity c (chiB d sb)) (sigma0 c (chiB d sb)) μ) :
    IsBlockFrobData 3 (lY c d sb) (lX c d sb) 0 (pairParity c (chiB d sb))
      (sigma0 c (chiB d sb)) μ :=
  data_swap (pre := []) (post := [RealBlock.character (chiA d sb)]) (c := c) (d := chiB d sb)
    rfl hs

/-- The inverse swap `K(c, χ_b, χ_a) → K(χ_b, c, χ_a)`. -/
theorem dataQ1' {μ : ℤ → ℂ}
    (hs : IsSymmetric (pairParity c (chiB d sb)) (sigma0 c (chiB d sb)) μ) :
    IsBlockFrobData 3 (lX c d sb) (lY c d sb) 0 (pairParity c (chiB d sb))
      (sigma0 c (chiB d sb))⁻¹ (fun k => (μ k)⁻¹) :=
  data_unswap (pre := []) (post := [RealBlock.character (chiA d sb)]) (c := c) (d := chiB d sb)
    rfl hs

/-- The swap `Q₂ : K(χ_b, χ_a, c) → K(χ_b, c, χ_a)` along the second block. -/
theorem dataQ2 {μ : ℤ → ℂ}
    (hs : IsSymmetric (pairParity c (chiA d sb)) (sigma0 c (chiA d sb)) μ) :
    IsBlockFrobData 3 (lZ c d sb) (lY c d sb) 1 (pairParity c (chiA d sb))
      (sigma0 c (chiA d sb)) μ :=
  data_swap (pre := [RealBlock.character (chiB d sb)]) (post := []) (c := c) (d := chiA d sb)
    rfl hs

/-- The inverse swap `K(χ_b, c, χ_a) → K(χ_b, χ_a, c)`. -/
theorem dataQ2' {μ : ℤ → ℂ}
    (hs : IsSymmetric (pairParity c (chiA d sb)) (sigma0 c (chiA d sb)) μ) :
    IsBlockFrobData 3 (lY c d sb) (lZ c d sb) 1 (pairParity c (chiA d sb))
      (sigma0 c (chiA d sb))⁻¹ (fun k => (μ k)⁻¹) :=
  data_unswap (pre := [RealBlock.character (chiB d sb)]) (post := []) (c := c) (d := chiA d sb)
    rfl hs

/-- The indicator `τ_j` of the modes `|j| ≥ ℓ`. -/
def highIndicator (j : ℤ) : ℂ := if |d.weight| ≤ |j| then 1 else 0

theorem isSymmetric_highIndicator (ε : ℤ) : IsSymmetric ε 1 (highIndicator d) := fun k _ => by
  simp only [highIndicator, abs_neg, one_mul]

/-- The projection onto the modes `|j| ≥ ℓ` along the second block, from `K(c, χ_b, χ_a)` to
`K(c, sgn^{s_b} |·|^a, sgn^{s_a} |·|^b)`. -/
theorem dataG :
    IsBlockFrobData 3 (lX c d sb) (lG c d sb) 1 (pairParity (chiB d sb) (chiA d sb)) 1
      (highIndicator d) := by
  refine IsBlockFrobData.of_mid (pre := [RealBlock.character c]) (post := [])
    (ws := [RealBlock.character (chiB d sb), RealBlock.character (chiA d sb)])
    (ws' := [RealBlock.character
        (RealJacquetFrobenius.charData (chiB d sb).parity (chiA d sb).exponent),
      RealBlock.character
        (RealJacquetFrobenius.charData (chiA d sb).parity (chiB d sb).exponent)])
    rfl rfl rfl rfl rfl ?_ (isSymmetric_highIndicator d _) ?_ ?_ ?_
  · rw [realPositionCharacter_neg_one, realPositionCharacter_neg_one,
      neg_one_pow_pairParity']
    rfl
  · rw [realPositionCharacter_neg_one, mul_one]
    rfl
  · rw [realPositionCharacter_neg_one, mul_one]
    rfl
  · intro e he
    simp [realInducedBlockAt] at he

end Data

/-! ## Sign equivariance of the projection -/

section Signs

theorem pow_eq_pow_mul_pow_of_sq {x : ℂ} (hx : x ^ 2 = 1) {k m e : ℕ}
    (h : k % 2 = (m + e) % 2) : x ^ k = x ^ m * x ^ e := by
  have key : ∀ q : ℕ, x ^ q = x ^ (q % 2) := fun q => by
    conv_lhs => rw [← Nat.mod_add_div q 2, pow_add, pow_mul, hx, one_pow, mul_one]
  rw [← pow_add, key k, key (m + e), h]

theorem posChar_signUnit (ds : List RealBlock) (i : ℕ) (x : ℝˣ) :
    realPositionCharacter ds i (signUnit x) =
      ((signReal (x : ℝ) : ℝ) : ℂ) ^ (realPositionSign ds i).val := by
  unfold signUnit signReal
  split_ifs
  · rw [RealStrictCharacterLanglandsQuotient.realPositionCharacter_one]
    simp
  · rw [realPositionCharacter_neg_one]
    simp

theorem signReal_sq (r : ℝ) : ((signReal r : ℝ) : ℂ) ^ 2 = 1 := by
  unfold signReal
  split_ifs <;> simp

theorem sgnDet_signDiagonal {N : ℕ} (a : Fin N → ℝˣ) :
    RealSwapFLanding.sgnDet N
        (Unitary.toUnits (PrincipalSeriesExtension.signDiagonal fun i => (a i : ℝ))) =
      ∏ i, ((signReal (a i : ℝ) : ℝ) : ℂ) := by
  have hdet : ((Unitary.toUnits (PrincipalSeriesExtension.signDiagonal fun i => (a i : ℝ)) :
      Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ).det =
        ∏ i, signReal (a i : ℝ) :=
    Matrix.det_diagonal
  have habs : |∏ i, signReal (a i : ℝ)| = 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_eq_one fun i _ => abs_signReal _
  rw [RealSwapFLanding.sgnDet, hdet, habs, div_one, Complex.ofReal_prod]

variable (c : RealCharacterData) (d : ComplexCharacterData) (sb : Fin 2)

/-- `c'' = sgn^{ε + s_a} |·|^s`: the character for which the landing statement is used. -/
def cPP : RealCharacterData :=
  RealJacquetFrobenius.charData (fin2 (c.parity.val + (chiA d sb).parity.val)) c.exponent

theorem cPP_parity_val :
    (cPP c d sb).parity.val = (c.parity.val + (sb.val + d.weight.natAbs + 1) % 2) % 2 := rfl

/-- **Sign equivariance.** A function of the standard module of
`[c, sgn^{s_b} |·|^a, sgn^{s_a} |·|^b]` transforms under the sign matrices as one of the
principal series of `[c'', d]`, twisted by the `s_a`-th power of the sign of the
determinant. -/
theorem sign_equivariance (G : KF 3 (lG c d sb)) (a : Fin 3 → ℝˣ)
    (κ : Matrix.unitaryGroup (Fin 3) ℝ) :
    (G : Langlands.GeneralLinear 3 ℝ → ℂ)
        (Unitary.toUnits (PrincipalSeriesExtension.signDiagonal (fun i => (a i : ℝ)) * κ)) =
      principalSeriesCharacter ℝ 3
          (realPositionCharacter [RealBlock.character (cPP c d sb), RealBlock.induced d])
          (fun i => signUnit (a i)) *
        RealSwapFLanding.sgnDet 3
            (Unitary.toUnits (PrincipalSeriesExtension.signDiagonal (fun i => (a i : ℝ)))) ^
          (chiA d sb).parity.val *
        (G : Langlands.GeneralLinear 3 ℝ → ℂ) (Unitary.toUnits κ) := by
  rw [PartialJacquet.signDiagonal_toUnits, G.2.1.1.2, JacquetKernel.principalSeriesCharacter_sign,
    JacquetKernel.principalSeriesCharacter_sign, sgnDet_signDiagonal, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [posChar_signUnit, posChar_signUnit]
  refine pow_eq_pow_mul_pow_of_sq (signReal_sq _) ?_
  fin_cases i <;> simp [realPositionSign, cPP, chiA, chiB, RealJacquetFrobenius.charData] <;> omega

end Signs

/-! ## The kernel of `T₀` -/

section Kernel

variable (c : RealCharacterData) (d : ComplexCharacterData) (sb : Fin 2)

theorem even_Q1_class :
    Even (pairParity c (chiB d sb) -
      ((d.weight.natAbs + 1 + (cPP c d sb).parity.val : ℕ) : ℤ)) := by
  have e1 : pairParity c (chiB d sb) = (((c.parity.val + sb.val) % 2 : ℕ) : ℤ) := rfl
  rw [e1, cPP_parity_val, Int.even_iff]
  omega

theorem sigma0_chiB :
    sigma0 c (chiB d sb) = (-1) ^ (d.weight.natAbs + 1 + (cPP c d sb).parity.val) := by
  have e1 : (pairParity c (chiB d sb)).natAbs = (c.parity.val + sb.val) % 2 := rfl
  rw [sigma0, e1, cPP_parity_val]
  exact neg_one_pow_congr (by omega)

/-- **The kernel step.** Assume the landing statement. Let `Q₂ : K(χ_b, χ_a, c) → K(χ_b, c, χ_a)`
and `Q₁ : K(χ_b, c, χ_a) → K(c, χ_b, χ_a)` be swaps with multipliers solving the recurrences of
the intertwiners. Then `D₁ ∘ Q₁ ∘ Q₂` vanishes on the kernel of `T₀`. -/
theorem kernel_step (hL : RealSwapLandingCharacterFirstStatement) (hl : 0 < d.weight.natAbs)
    {μ₀ μ₁ : ℤ → ℂ}
    (hQ1 : IsBlockFrobData 3 (lY c d sb) (lX c d sb) 0 (pairParity c (chiB d sb))
      (sigma0 c (chiB d sb)) μ₀)
    (hQ2 : IsBlockFrobData 3 (lZ c d sb) (lY c d sb) 1 (pairParity c (chiA d sb))
      (sigma0 c (chiA d sb)) μ₁)
    (hμ₀ : IsRecurrent ((chiB d sb).exponent - c.exponent + 1) (pairParity c (chiB d sb)) μ₀)
    (hμ₁ : IsRecurrent ((chiA d sb).exponent - c.exponent + 1) (pairParity c (chiA d sb)) μ₁)
    (z : KF 3 (lZ c d sb)) (hz : blockFrobMap (dataT0 c d sb hl) z = 0) :
    blockFrobMap (dataD1 c d sb hl) (blockFrobMap hQ1 (blockFrobMap hQ2 z)) = 0 := by
  have hεba := pairParity_eq (chiB d sb) (chiA d sb)
  have hpar := even_pairParity_chiB_chiA d sb
  have hσ := neg_one_pow_sq_fin (chiA d sb).parity
  have habs : |d.weight| = (d.weight.natAbs : ℤ) := Int.abs_eq_natAbs d.weight
  -- the high modes of `z` along the first block vanish
  have hf0 : ∀ j : ℤ, |d.weight| ≤ |j| → ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 0 j (z : Langlands.GeneralLinear 3 ℝ → ℂ) x = 0 := by
    intro j hj x hx
    by_cases hje : Even (j - pairParity (chiB d sb) (chiA d sb))
    · have e := blockFourierCoefficient_blockFrobMap (dataT0 c d sb hl) z hx j
      rw [hz, ZeroMemClass.coe_zero, blockFourierCoefficient_zero] at e
      refine (mul_eq_zero.mp e.symm).resolve_left
        ((tailMultiplier_ne_zero_iff hl hεba hpar hσ hje).mpr ?_)
      rw [habs] at hj
      rcases hj.lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd heq.le (not_le.mpr (abs_lt_of_parity hpar hje heq.symm.le))
    · exact blockFourierCoefficient_eq_zero_of_not_even (dataT0 c d sb hl).lt
        (dataT0 c d sb hl).par z hje x
  have hδ : (chiB d sb).exponent - c.exponent + 1 + (d.weight.natAbs : ℂ) =
      (chiA d sb).exponent - c.exponent + 1 := by
    rw [chiA_exponent, chiB_exponent]
    ring
  have hμ₁' : IsRecurrent ((chiB d sb).exponent - c.exponent + 1 + (d.weight.natAbs : ℂ))
      ((cPP c d sb).parity.val : ℤ) μ₁ := by
    rw [hδ]
    exact hμ₁
  set g₁ := blockFrobMap hQ2 z with hg₁
  set g := blockFrobMap hQ1 g₁ with hg
  set G := blockFrobMap (dataG c d sb) g with hG
  have hhigh := RealSwapFLanding.highModes_eq_zero hL (cPP c d sb) d
    ((chiB d sb).exponent - c.exponent + 1) μ₀ μ₁
    (isRecurrent_of_even hμ₀ (even_Q1_class c d sb))
    (isSymmetric_of_even hQ1.sym (even_Q1_class c d sb) (sigma0_chiB c d sb))
    hμ₁' hQ2.sym (chiA d sb).parity.val
    (continuous_coe z) (continuous_coe g₁) (continuous_coe g) (continuous_coe G)
    z.2.2 g₁.2.2 g.2.2 G.2.2 hf0
    (fun j x hx => blockFourierCoefficient_blockFrobMap hQ2 z hx j)
    (fun j x hx => blockFourierCoefficient_blockFrobMap hQ1 g₁ hx j)
    (fun j hj x hx => by
      rw [hG, blockFourierCoefficient_blockFrobMap (dataG c d sb) g hx j, highIndicator,
        ite_eq_left hj, one_mul])
    (fun j hj x hx => by
      rw [hG, blockFourierCoefficient_blockFrobMap (dataG c d sb) g hx j, highIndicator,
        ite_eq_right (not_le.mpr hj), zero_mul])
    (sign_equivariance c d sb G)
  refine eq_of_blockFourierCoefficient_eq (dataD1 c d sb hl).lt fun j x hx => ?_
  rw [ZeroMemClass.coe_zero, blockFourierCoefficient_zero]
  by_cases hj : |d.weight| ≤ |j|
  · rw [blockFourierCoefficient_blockFrobMap (dataD1 c d sb hl) g hx j, hhigh j hj x hx,
      mul_zero]
  · exact (blockFrobMap (dataD1 c d sb hl) g).2.1.2 1 (dP d sb) rfl j
      (by rw [dP_abs_weight, ← habs]; exact not_le.mp hj) x

end Kernel

/-! ## Descent along a tail map and assembly -/

section Descent

variable {n : ℕ}

/-- **Descent.** Let `T : K(es) → K(es')` be an exact intertwiner with a right inverse `S`,
and `P` an intertwiner modulo `M` out of `K(es)` that vanishes on the kernel of `T`. Then
`P ∘ S` is an intertwiner modulo `M` out of `K(es')`, and `P ∘ S ∘ T = P`. -/
theorem descend {es es' ds : List RealBlock} {M : Submodule ℂ (KF n ds)}
    {P : KF n es →ₗ[ℂ] KF n ds} {T : KF n es →ₗ[ℂ] KF n es'} {S : KF n es' →ₗ[ℂ] KF n es}
    (hP : IsRealIntertwinerModulo n es ds M P) (hT : IsRealIntertwinerModulo n es es' ⊥ T)
    (hTS : ∀ g, T (S g) = g) (hker : ∀ z, T z = 0 → P z = 0) :
    IsRealIntertwinerModulo n es' ds M (P ∘ₗ S) ∧ ∀ z, P (S (T z)) = P z := by
  have hfac : ∀ z, P (S (T z)) = P z := fun z => by
    have h := hker (z - S (T z)) (by rw [map_sub, hTS, sub_self])
    rw [map_sub, sub_eq_zero] at h
    exact h.symm
  exact ⟨modulo_of_comp_surjective hP hT (fun g => ⟨S g, hTS g⟩)
    (LinearMap.ext fun z => hfac z), hfac⟩

/-- With `P ∘ S ∘ T = P`, the maps `P ∘ S` and `P` have the same range. -/
theorem range_comp_eq {es es' ds : List RealBlock} {P : KF n es →ₗ[ℂ] KF n ds}
    {T : KF n es →ₗ[ℂ] KF n es'} {S : KF n es' →ₗ[ℂ] KF n es}
    (hfac : ∀ z, P (S (T z)) = P z) : LinearMap.range (P ∘ₗ S) = LinearMap.range P := by
  refine le_antisymm (LinearMap.range_comp_le_range S P) ?_
  rintro _ ⟨z, rfl⟩
  exact ⟨T z, hfac z⟩

/-- A Frobenius map with the generic multiplier `genericMultiplier ν ε`, where
`ν = t_p - t_{p+1}` and the numerators and denominators of the multiplier do not vanish, is an
exact intertwiner with a right inverse (the map with the inverse multiplier). -/
theorem generic_swap {ds es : List RealBlock} {p : ℕ} {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    {ν σ : ℂ} (h : IsBlockFrobData n ds es p ε σ (genericMultiplier ν ε))
    (h' : IsBlockFrobData n es ds p ε σ⁻¹ fun k => (genericMultiplier ν ε k)⁻¹)
    (hδ : GramFormula.realPositionExponent ds p -
      GramFormula.realPositionExponent ds (p + 1) = ν)
    (hd : ∀ i : ℕ, (ε : ℂ) + 2 * i + 1 + ν ≠ 0) (hne : ∀ m : ℕ, ν ≠ (ε : ℂ) + 2 * m + 1) :
    IsRealIntertwinerModulo n ds es ⊥ (blockFrobMap h) ∧
      ∀ g, blockFrobMap h (blockFrobMap h' g) = g :=
  ⟨isRealIntertwinerModulo_blockFrobMap h
      (by rw [hδ]; exact isRecurrent_genericMultiplier' hε hd) ⊥,
    frob_inv_of_ne_zero h h' fun k _ => genericMultiplier_ne_zero' hd hne k⟩

/-- **One piece.** An exact intertwiner `P : K(Z) → K(V)` onto, vanishing on the kernel of
an exact intertwiner `T : K(Z) → K(W)` with a right inverse, gives a filtration of `K(V)`
with the single piece `W`. -/
theorem hasFiltration_of_stage {V Z W : List RealBlock}
    (P : KF n Z →ₗ[ℂ] KF n V) (T : KF n Z →ₗ[ℂ] KF n W) (S : KF n W →ₗ[ℂ] KF n Z)
    (hP : IsRealIntertwinerModulo n Z V ⊥ P) (hPs : Function.Surjective P)
    (hT : IsRealIntertwinerModulo n Z W ⊥ T) (hTS : ∀ g, T (S g) = g)
    (hker : ∀ z, T z = 0 → P z = 0) :
    HasFiltration n V (fun es => es = W) := by
  obtain ⟨hq₀, hfac⟩ := descend hP hT hTS hker
  refine (HasFiltration.self (P := fun es => es = W) rfl).map (P ∘ₗ S) hq₀ fun g => ?_
  obtain ⟨z, rfl⟩ := hPs g
  exact ⟨T z, hfac z⟩

/-- **Two pieces.** Let `A : K(Y) → K(V)` be an exact intertwiner onto and
`Q : K(Z) → K(Y)` an exact intertwiner such that `A ∘ Q` vanishes on the kernel of an exact
intertwiner `T : K(Z) → K(W)` with a right inverse `S`. Let `q : K(R) → K(Y)` be an
intertwiner modulo the range of `Q` with a left inverse `D` whose kernel lies in the range of
`Q`. Then `K(V)` has a filtration with the pieces `W` (by `A ∘ Q ∘ S`) and `R` (by
`A ∘ q`). -/
theorem hasFiltration_of_stages {V Y Z W R : List RealBlock}
    (A : KF n Y →ₗ[ℂ] KF n V) (Q : KF n Z →ₗ[ℂ] KF n Y) (T : KF n Z →ₗ[ℂ] KF n W)
    (S : KF n W →ₗ[ℂ] KF n Z) (D : KF n Y →ₗ[ℂ] KF n R) (q : KF n R →ₗ[ℂ] KF n Y)
    (hA : IsRealIntertwinerModulo n Y V ⊥ A) (hAs : Function.Surjective A)
    (hQ : IsRealIntertwinerModulo n Z Y ⊥ Q) (hT : IsRealIntertwinerModulo n Z W ⊥ T)
    (hTS : ∀ g, T (S g) = g) (hker : ∀ z, T z = 0 → A (Q z) = 0)
    (hq : IsRealIntertwinerModulo n R Y (LinearMap.range Q) q)
    (hDq : ∀ f, D (q f) = f) (hkerD : LinearMap.ker D ≤ LinearMap.range Q) :
    HasFiltration n V (fun es => es = W ∨ es = R) := by
  obtain ⟨hq₀, hfac⟩ := descend (P := A ∘ₗ Q) (modulo_comp_bot hA hQ) hT hTS hker
  refine hasFiltration_two (Or.inl rfl) (Or.inr rfl) _ (A ∘ₗ q) hq₀ ?_ ?_
  · refine modulo_mono (modulo_comp hA hq) ?_
    rw [bot_sup_eq, ← LinearMap.range_comp]
    exact (range_comp_eq hfac).ge
  · intro g
    obtain ⟨y, rfl⟩ := hAs g
    have hy : y - q (D y) ∈ LinearMap.ker D := by
      rw [LinearMap.mem_ker, map_sub, hDq, sub_self]
    obtain ⟨z, hz⟩ := hkerD hy
    refine ⟨T z, D y, ?_⟩
    have e1 : ((A ∘ₗ Q) ∘ₗ S) (T z) = A y - A (q (D y)) := by
      rw [LinearMap.comp_apply, hfac, LinearMap.comp_apply, hz, map_sub]
    rw [e1, LinearMap.comp_apply, sub_add_cancel]

end Descent

/-! ## The maps `D₁`, `T₀` and the first swap -/

section Maps

variable (c : RealCharacterData) (d : ComplexCharacterData) (sb : Fin 2)

theorem tail_recurrent (hl : 0 < d.weight.natAbs) :
    IsRecurrent ((chiB d sb).exponent - (chiA d sb).exponent + 1)
      (pairParity (chiB d sb) (chiA d sb))
      (tailMultiplier d.weight.natAbs (pairParity (chiB d sb) (chiA d sb))
        ((-1) ^ (chiA d sb).parity.val)) := by
  rw [show (chiB d sb).exponent - (chiA d sb).exponent + 1 = 1 - (d.weight.natAbs : ℂ) by
    linear_combination -(chiA_sub_chiB d sb)]
  exact isRecurrent_tailMultiplier hl (pairParity_eq _ _) (even_pairParity_chiB_chiA d sb)
    (neg_one_pow_sq_fin _)

theorem posExp_lX_1 : GramFormula.realPositionExponent (lX c d sb) 1 = (chiB d sb).exponent :=
  rfl

theorem posExp_lX_2 : GramFormula.realPositionExponent (lX c d sb) (1 + 1) =
    (chiA d sb).exponent :=
  rfl

theorem posExp_lZ_0 : GramFormula.realPositionExponent (lZ c d sb) 0 = (chiB d sb).exponent :=
  rfl

theorem posExp_lZ_1 : GramFormula.realPositionExponent (lZ c d sb) (0 + 1) =
    (chiA d sb).exponent :=
  rfl

theorem modulo_D1 (hl : 0 < d.weight.natAbs) :
    IsRealIntertwinerModulo 3 (lX c d sb) (lV c d sb) ⊥ (blockFrobMap (dataD1 c d sb hl)) := by
  refine isRealIntertwinerModulo_blockFrobMap (dataD1 c d sb hl) ?_ ⊥
  rw [posExp_lX_1, posExp_lX_2]
  exact tail_recurrent d sb hl

theorem modulo_T0 (hl : 0 < d.weight.natAbs) :
    IsRealIntertwinerModulo 3 (lZ c d sb) (lW c d sb) ⊥ (blockFrobMap (dataT0 c d sb hl)) := by
  refine isRealIntertwinerModulo_blockFrobMap (dataT0 c d sb hl) ?_ ⊥
  rw [posExp_lZ_0, posExp_lZ_1]
  exact tail_recurrent d sb hl

theorem D1_S1 (hl : 0 < d.weight.natAbs) (g : KF 3 (lV c d sb)) :
    blockFrobMap (dataD1 c d sb hl) (blockFrobMap (dataS1 c d sb hl) g) = g :=
  tail_inv hl (pairParity_eq _ _) (even_pairParity_chiB_chiA d sb) (neg_one_pow_sq_fin _)
    (dataD1 c d sb hl) (dataS1 c d sb hl) (dI := dP d sb) rfl (dP_abs_weight d sb) g

theorem T0_S0 (hl : 0 < d.weight.natAbs) (g : KF 3 (lW c d sb)) :
    blockFrobMap (dataT0 c d sb hl) (blockFrobMap (dataS0 c d sb hl) g) = g :=
  tail_inv hl (pairParity_eq _ _) (even_pairParity_chiB_chiA d sb) (neg_one_pow_sq_fin _)
    (dataT0 c d sb hl) (dataS0 c d sb hl) (dI := dP d sb) rfl (dP_abs_weight d sb) g

/-- The generic multiplier of the first swap, `ν₀ = b - s`. -/
abbrev mu0 : ℤ → ℂ :=
  genericMultiplier ((chiB d sb).exponent - c.exponent) (pairParity c (chiB d sb))

/-- The generic multiplier of the second swap, `ν₁ = a - s`. -/
abbrev mu1 : ℤ → ℂ :=
  genericMultiplier ((chiA d sb).exponent - c.exponent) (pairParity c (chiA d sb))

theorem symm_mu0 :
    IsSymmetric (pairParity c (chiB d sb)) (sigma0 c (chiB d sb)) (mu0 c d sb) :=
  isSymmetric_genericMultiplier _ (pairParity_eq _ _)

theorem symm_mu1 :
    IsSymmetric (pairParity c (chiA d sb)) (sigma0 c (chiA d sb)) (mu1 c d sb) :=
  isSymmetric_genericMultiplier _ (pairParity_eq _ _)

/-- **Stage 1.** When the generic multiplier of the first swap has no vanishing numerators or
denominators, `D₁ ∘ Q₁ : K(χ_b, c, χ_a) → K(c, d')` is an exact intertwiner onto. -/
theorem stage1 (hl : 0 < d.weight.natAbs)
    (hd : ∀ i : ℕ, (pairParity c (chiB d sb) : ℂ) + 2 * i + 1 +
      ((chiB d sb).exponent - c.exponent) ≠ 0)
    (hne : ∀ m : ℕ, (chiB d sb).exponent - c.exponent ≠
      (pairParity c (chiB d sb) : ℂ) + 2 * m + 1) :
    IsRealIntertwinerModulo 3 (lY c d sb) (lV c d sb) ⊥
        (blockFrobMap (dataD1 c d sb hl) ∘ₗ blockFrobMap (dataQ1 c d sb (symm_mu0 c d sb))) ∧
      Function.Surjective
        (blockFrobMap (dataD1 c d sb hl) ∘ₗ blockFrobMap (dataQ1 c d sb (symm_mu0 c d sb))) := by
  obtain ⟨hQ, hinv⟩ := generic_swap (pairParity_eq _ _) (dataQ1 c d sb (symm_mu0 c d sb))
    (dataQ1' c d sb (symm_mu0 c d sb)) rfl hd hne
  refine ⟨modulo_comp_bot (modulo_D1 c d sb hl) hQ, fun g =>
    ⟨blockFrobMap (dataQ1' c d sb (symm_mu0 c d sb)) (blockFrobMap (dataS1 c d sb hl) g), ?_⟩⟩
  rw [LinearMap.comp_apply, hinv, D1_S1 c d sb hl]

end Maps

/-! ## The pieces -/

section Pieces

variable (c : RealCharacterData) (d : ComplexCharacterData) (sb : Fin 2)

/-- `R = [χ_b, induced(c, χ_a)]` for the weight `ℓ'` of the induction block. -/
abbrev lR (ℓ' : ℕ) : List RealBlock :=
  [RealBlock.character (chiB d sb), RealBlock.induced (pairInduced c (chiA d sb) ℓ')]

theorem piece_W : IsAdjacentPiece [] [] (RealBlock.character c) (RealBlock.induced d)
    [RealBlock.induced d, RealBlock.character c] :=
  ⟨[RealBlock.induced d, RealBlock.character c], rfl, Or.inl rfl⟩

/-- `R` is an adjacent piece when `t_{χ_a} - s = ℓ' > ℓ`: its exponent support
`[b, a, s]` is the reverse of `[s, a, b]`, and `ℓ² < ℓ'²`. -/
theorem piece_R {ℓ' : ℕ} (hν : (chiA d sb).exponent - c.exponent = ℓ')
    (hlt : d.weight.natAbs < ℓ') :
    IsAdjacentPiece [] [] (RealBlock.character c) (RealBlock.induced d) (lR c d sb ℓ') := by
  refine ⟨lR c d sb ℓ', rfl, Or.inr ⟨?_, ?_⟩⟩
  · have e : realExponentSupport (lR c d sb ℓ') = (chiB d sb).exponent ::
        realExponentSupport [RealBlock.induced (pairInduced c (chiA d sb) ℓ')] := rfl
    rw [e, realExponentSupport_pairInduced_eq hν]
    exact List.reverse_perm [c.exponent, (chiA d sb).exponent, (chiB d sb).exponent]
  · simp only [realWeightSquareSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      realBlockWeightSquare, pairInduced_weight, Int.natAbs_natCast, zero_add, add_zero]
    exact Nat.pow_lt_pow_left hlt two_ne_zero

/-- A filtration of `K(c, d')` whose pieces have the `O(3)`-finite functions of adjacent
pieces is an adjacent filtration of `[c, d]`. -/
theorem realAdjacentFiltration_of_lV {P : List RealBlock → Prop}
    (h : HasFiltration 3 (lV c d sb) P)
    (hP : ∀ es, P es → ∃ es', IsAdjacentPiece [] [] (RealBlock.character c)
      (RealBlock.induced d) es' ∧ KF 3 es' = KF 3 es) :
    RealAdjacentFiltration 3 [] [] (RealBlock.character c) (RealBlock.induced d) :=
  (realAdjacentFiltration_iff 3 [] [] _ _).mpr ((h.congr (kf_V c d sb)).of_eq_pieces hP)

end Pieces

/-! ## The two cases -/

section Cases

variable (c : RealCharacterData) (d : ComplexCharacterData) (sb : Fin 2)

/-- **Case (a).** Assume the landing statement, `ℓ > 0`, that `w = b - s` is an integer only
if `w = 0`, and `ε + s_b` odd. Then `[c, d]` has the adjacent filtration with the single piece
`[d, c]`. -/
theorem filtration_generic (hL : RealSwapLandingCharacterFirstStatement)
    (hl : 0 < d.weight.natAbs)
    (hw : ∀ k : ℤ, (chiB d sb).exponent - c.exponent = k → k = 0)
    (hsb : (c.parity.val + sb.val) % 2 = 1) :
    RealAdjacentFiltration 3 [] [] (RealBlock.character c) (RealBlock.induced d) := by
  have hε₀ := pairParity_nonneg c (chiB d sb)
  have hε₁ := pairParity_nonneg c (chiA d sb)
  have e₁ : pairParity c (chiA d sb) =
      (((c.parity.val + (sb.val + d.weight.natAbs + 1) % 2) % 2 : ℕ) : ℤ) := rfl
  have hd₀ : ∀ i : ℕ, (pairParity c (chiB d sb) : ℂ) + 2 * i + 1 +
      ((chiB d sb).exponent - c.exponent) ≠ 0 := fun i h => by
    have := hw (-(pairParity c (chiB d sb) + 2 * i + 1)) (by push_cast; linear_combination h)
    omega
  have hne₀ : ∀ m : ℕ, (chiB d sb).exponent - c.exponent ≠
      (pairParity c (chiB d sb) : ℂ) + 2 * m + 1 := fun m h => by
    have := hw (pairParity c (chiB d sb) + 2 * m + 1) (by push_cast; exact h)
    omega
  have hd₁ : ∀ i : ℕ, (pairParity c (chiA d sb) : ℂ) + 2 * i + 1 +
      ((chiA d sb).exponent - c.exponent) ≠ 0 := fun i h => by
    have := hw (-(pairParity c (chiA d sb) + 2 * i + 1 + d.weight.natAbs))
      (by push_cast; linear_combination h - chiA_sub_chiB d sb - Nat.cast_natAbs (α := ℂ) d.weight)
    omega
  have hne₁ : ∀ m : ℕ, (chiA d sb).exponent - c.exponent ≠
      (pairParity c (chiA d sb) : ℂ) + 2 * m + 1 := fun m h => by
    have := hw (pairParity c (chiA d sb) + 2 * m + 1 - d.weight.natAbs)
      (by push_cast; linear_combination h - chiA_sub_chiB d sb - Nat.cast_natAbs (α := ℂ) d.weight)
    rw [e₁] at this
    omega
  obtain ⟨hA, hAs⟩ := stage1 c d sb hl hd₀ hne₀
  obtain ⟨hQ2, hinv2⟩ := generic_swap (pairParity_eq _ _) (dataQ2 c d sb (symm_mu1 c d sb))
    (dataQ2' c d sb (symm_mu1 c d sb)) rfl hd₁ hne₁
  refine realAdjacentFiltration_of_lV c d sb
    (hasFiltration_of_stage _ _ _ (modulo_comp_bot hA hQ2) (fun g => ?_) (modulo_T0 c d sb hl)
      (T0_S0 c d sb hl) fun z hz => kernel_step c d sb hL hl
        (dataQ1 c d sb (symm_mu0 c d sb)) (dataQ2 c d sb (symm_mu1 c d sb))
        (isRecurrent_genericMultiplier' (pairParity_eq _ _) hd₀)
        (isRecurrent_genericMultiplier' (pairParity_eq _ _) hd₁) z hz)
    fun es hes => ⟨_, piece_W c d, by rw [hes]; exact (kf_W c d sb).symm⟩
  obtain ⟨y, rfl⟩ := hAs g
  exact ⟨blockFrobMap (dataQ2' c d sb (symm_mu1 c d sb)) y, by
    rw [LinearMap.comp_apply, hinv2]⟩

/-- **Case (b).** Assume the landing statement, `ℓ > 0`, that `w = b - s = k` is a positive
integer, and `ε + s_b ≡ k (mod 2)`. Then `[c, d]` has the adjacent filtration with the pieces
`[d, c]` and `[χ_b, induced(c, χ_a)]` (weight `k + ℓ`). -/
theorem filtration_reducible (hL : RealSwapLandingCharacterFirstStatement)
    (hl : 0 < d.weight.natAbs) {k : ℕ} (hk0 : 0 < k)
    (hk : (chiB d sb).exponent - c.exponent = k) (hsb : (c.parity.val + sb.val) % 2 = k % 2) :
    RealAdjacentFiltration 3 [] [] (RealBlock.character c) (RealBlock.induced d) := by
  have hε₀ := pairParity_nonneg c (chiB d sb)
  have e₀ : pairParity c (chiB d sb) = (((c.parity.val + sb.val) % 2 : ℕ) : ℤ) := rfl
  have e₁ : pairParity c (chiA d sb) =
      (((c.parity.val + (sb.val + d.weight.natAbs + 1) % 2) % 2 : ℕ) : ℤ) := rfl
  -- stage 1 is generic
  have hd₀ : ∀ i : ℕ, (pairParity c (chiB d sb) : ℂ) + 2 * i + 1 +
      ((chiB d sb).exponent - c.exponent) ≠ 0 := fun i h => by
    rw [hk] at h
    have : pairParity c (chiB d sb) + 2 * i + 1 + k = 0 := by exact_mod_cast h
    omega
  have hne₀ : ∀ m : ℕ, (chiB d sb).exponent - c.exponent ≠
      (pairParity c (chiB d sb) : ℂ) + 2 * m + 1 := fun m h => by
    rw [hk] at h
    have : (k : ℤ) = pairParity c (chiB d sb) + 2 * m + 1 := by exact_mod_cast h
    rw [e₀] at this
    omega
  -- stage 2 is reducible, with `t_{χ_a} - s = ℓ' = k + ℓ`
  obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : ℕ, ℓ' = k + d.weight.natAbs := ⟨_, rfl⟩
  have hℓ'0 : 0 < ℓ' := by omega
  have hε₁ := pairParity_eq c (chiA d sb)
  have hpar₁ : Even ((ℓ' : ℤ) - 1 - pairParity c (chiA d sb)) := by
    rw [e₁, Int.even_iff]
    omega
  have hν₁ : (chiA d sb).exponent - c.exponent = (ℓ' : ℂ) := by
    rw [hℓ', Nat.cast_add]
    linear_combination hk + chiA_sub_chiB d sb
  have hσ₁ := neg_one_pow_sq_fin (chiA d sb).parity
  have hs₁ : IsSymmetric (pairParity c (chiA d sb)) (sigma0 c (chiA d sb))
      (binomialMultiplier ℓ' (pairParity c (chiA d sb))) :=
    isSymmetric_binomialMultiplier ℓ' hε₁
  have hQ2d := dataQ2 c d sb hs₁
  have hBd := dataQ2' c d sb hs₁
  have hrec₁ : IsRecurrent ((chiA d sb).exponent - c.exponent + 1) (pairParity c (chiA d sb))
      (binomialMultiplier ℓ' (pairParity c (chiA d sb))) := by
    rw [hν₁]
    exact isRecurrent_binomialMultiplier hℓ'0 hε₁ hpar₁
  have hQ2 : IsRealIntertwinerModulo 3 (lZ c d sb) (lY c d sb) ⊥ (blockFrobMap hQ2d) :=
    isRealIntertwinerModulo_blockFrobMap hQ2d hrec₁ ⊥
  have hDd : IsBlockFrobData 3 (lY c d sb) (lR c d sb ℓ') 1 (pairParity c (chiA d sb))
      ((-1) ^ (chiA d sb).parity.val)
      (tailMultiplier ℓ' (pairParity c (chiA d sb)) ((-1) ^ (chiA d sb).parity.val)) :=
    data_D (pre := [RealBlock.character (chiB d sb)]) (post := []) (c := c) (d := chiA d sb)
      rfl hℓ'0 hpar₁ hν₁
  have hq1d : IsBlockFrobData 3 (lR c d sb ℓ') (lY c d sb) 1 (pairParity c (chiA d sb))
      ((-1) ^ (chiA d sb).parity.val)⁻¹
      (fun j => (tailMultiplier ℓ' (pairParity c (chiA d sb))
        ((-1) ^ (chiA d sb).parity.val) j)⁻¹) :=
    data_q1 (pre := [RealBlock.character (chiB d sb)]) (post := []) (c := c) (d := chiA d sb)
      rfl hℓ'0 hpar₁ hν₁
  have hrecD : IsRecurrent (GramFormula.realPositionExponent (lY c d sb) 1 -
      GramFormula.realPositionExponent (lY c d sb) (1 + 1) + 1) (pairParity c (chiA d sb))
      (tailMultiplier ℓ' (pairParity c (chiA d sb)) ((-1) ^ (chiA d sb).parity.val)) := by
    show IsRecurrent (c.exponent - (chiA d sb).exponent + 1) _ _
    rw [show c.exponent - (chiA d sb).exponent + 1 = 1 - (ℓ' : ℂ) by
      linear_combination -hν₁]
    exact isRecurrent_tailMultiplier hℓ'0 hε₁ hpar₁ hσ₁
  have hinvD : ∀ f, blockFrobMap hDd (blockFrobMap hq1d f) = f :=
    tail_inv hℓ'0 hε₁ hpar₁ hσ₁ hDd hq1d (dI := pairInduced c (chiA d sb) ℓ') rfl
      (by rw [pairInduced_weight]; exact abs_of_nonneg (Int.natCast_nonneg _))
  have hkerD : LinearMap.ker (blockFrobMap hDd) ≤ LinearMap.range (blockFrobMap hQ2d) :=
    ker_tail_le_range hℓ'0 hε₁ hpar₁ hσ₁ hQ2d hBd hDd
  have hq1 : IsRealIntertwinerModulo 3 (lR c d sb ℓ') (lY c d sb)
      (LinearMap.range (blockFrobMap hQ2d)) (blockFrobMap hq1d) :=
    isRealIntertwinerModulo_of_leftInverse hq1d hDd hrecD hinvD _ hkerD
  obtain ⟨hA, hAs⟩ := stage1 c d sb hl hd₀ hne₀
  refine realAdjacentFiltration_of_lV c d sb
    (hasFiltration_of_stages _ _ _ _ _ _ hA hAs hQ2 (modulo_T0 c d sb hl) (T0_S0 c d sb hl)
      (fun z hz => kernel_step c d sb hL hl (dataQ1 c d sb (symm_mu0 c d sb)) hQ2d
        (isRecurrent_genericMultiplier' (pairParity_eq _ _) hd₀) hrec₁ z hz)
      hq1 hinvD hkerD) ?_
  rintro es (rfl | rfl)
  · exact ⟨_, piece_W c d, (kf_W c d sb).symm⟩
  · exact ⟨_, piece_R c d sb hν₁ (by omega), rfl⟩

end Cases

end RealCharacterInducedPushforward

end Langlands.Archimedean
