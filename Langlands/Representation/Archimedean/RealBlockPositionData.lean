import Langlands.Representation.Archimedean.PrincipalSeriesGramFormula
import Langlands.Representation.Archimedean.RealBlockFourierPropagation
import Langlands.Representation.Archimedean.RealBlockJacquetFunctional
import Langlands.Representation.Archimedean.RealStandardModuleGKModule

/-!
# Signs and exponents at the positions of a list of real blocks

The position characters `realPositionCharacter ds i` of a list of real blocks are of the form
`x ↦ sgn(x)^e |x|^t`. This file records the sign `realPositionSign ds i` and the exponent
`GramFormula.realPositionExponent ds i` at every position (`realPositionCharacter_eq_charFun`), their
behaviour under concatenation of lists, and two consequences used to build intertwining maps
between real standard modules by Frobenius reciprocity:

* `mem_realStandardModule_of_unitaryCompact`: a function of the principal series of the
  position characters lies in the standard module as soon as the Fourier conditions at the
  induction blocks hold on `O(N)`;
* `frobFun_mem_kFiniteFunctions`: the Frobenius function of a functional with the signs of
  the target list, the `ρ`-shifted exponents `shiftedExponent N ds` of the target list, and the
  Fourier conditions on `O(N)`, is an `O(N)`-finite function of the standard module.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option backward.isDefEq.respectTransparency false

namespace RealBlockPosition

open RealJacquetFrobenius RealBlockRotation RealBlockDerivative RealBlockPropagation
open RealBlockFourierFinite

/-! ## Signs and exponents -/

/-- The sign `e` of the position character `x ↦ sgn(x)^e |x|^t` at each position: the parity
of a character block; `|m| + 1 (mod 2)` and `0` at the two positions of the real induction of
a character of weight `m`; `0` past the end. -/
def realPositionSign : List RealBlock → ℕ → Fin 2
  | [], _ => 0
  | .character d :: _, 0 => d.parity
  | .character _ :: ds, p + 1 => realPositionSign ds p
  | .induced d :: _, 0 => ⟨(d.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩
  | .induced _ :: _, 1 => 0
  | .induced _ :: ds, p + 2 => realPositionSign ds p

/-- `(x/|x|)^k = (x/|x|)^(k mod 2)` for real `x ≠ 0`. -/
theorem sign_pow_eq_pow_mod_two {x : ℝ} (hx : x ≠ 0) (k : ℕ) :
    (((x / |x| : ℝ)) : ℂ) ^ k = (((x / |x| : ℝ)) : ℂ) ^ (k % 2) := by
  have hsq : (((x / |x| : ℝ)) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, div_pow, sq_abs, div_self (pow_ne_zero 2 hx), Complex.ofReal_one]
  conv_lhs => rw [← Nat.div_add_mod k 2, pow_add, pow_mul, hsq, one_pow, one_mul]

/-- The position characters are `x ↦ sgn(x)^e |x|^t` with the position signs and exponents. -/
theorem realPositionCharacter_eq_charFun :
    ∀ (ds : List RealBlock) (i : ℕ) (x : ℝˣ),
      realPositionCharacter ds i x =
        charFun (realPositionSign ds i) (GramFormula.realPositionExponent ds i) x
  | [], _, x => by simp [realPositionCharacter, realPositionSign, GramFormula.realPositionExponent, charFun]
  | .character d :: _, 0, x => by
      simp only [realPositionCharacter, realPositionSign, GramFormula.realPositionExponent, charFun]
      exact d.character_eq x
  | .character _ :: ds, p + 1, x => by
      simp only [realPositionCharacter, realPositionSign, GramFormula.realPositionExponent]
      exact realPositionCharacter_eq_charFun ds p x
  | .induced d :: _, 0, x => by
      simp only [realPositionCharacter, realPositionSign, GramFormula.realPositionExponent, charFun,
        realInducedFirstCharacter]
      rw [sign_pow_eq_pow_mod_two x.ne_zero]
  | .induced d :: _, 1, x => by
      simp [realPositionCharacter, realPositionSign, GramFormula.realPositionExponent, charFun,
        realInducedSecondCharacter]
  | .induced _ :: ds, p + 2, x => by
      simp only [realPositionCharacter, realPositionSign, GramFormula.realPositionExponent]
      exact realPositionCharacter_eq_charFun ds p x

theorem realPositionCharacter_neg_one (ds : List RealBlock) (i : ℕ) :
    realPositionCharacter ds i (-1) = (-1) ^ (realPositionSign ds i).val := by
  rw [realPositionCharacter_eq_charFun, Units.val_neg, Units.val_one, charFun_neg_one]

theorem realPositionCharacter_exp (ds : List RealBlock) (i : ℕ) (x : ℝ) :
    realPositionCharacter ds i (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') =
      Complex.exp (GramFormula.realPositionExponent ds i * x) := by
  rw [realPositionCharacter_eq_charFun, Units.val_mk0, charFun_exp, mul_comm]

/-! ## Concatenation -/

theorem realPositionSign_append :
    ∀ (ds es : List RealBlock) (i : ℕ),
      realPositionSign (ds ++ es) i =
        if i < realRank ds then realPositionSign ds i else realPositionSign es (i - realRank ds)
  | [], es, i => by simp
  | .character d :: ds, es, 0 => by simp [realPositionSign, RealBlock.rank]
  | .character d :: ds, es, i + 1 => by
      simp only [List.cons_append, realPositionSign, realRank_cons, RealBlock.rank]
      rw [realPositionSign_append ds es i]
      split_ifs with h1 h2 h2
      · rfl
      · omega
      · omega
      · congr 1
        omega
  | .induced d :: ds, es, 0 => by simp [realPositionSign, RealBlock.rank]
  | .induced d :: ds, es, 1 => by
      simp [realPositionSign, RealBlock.rank]
      intro h
      omega
  | .induced d :: ds, es, i + 2 => by
      simp only [List.cons_append, realPositionSign, realRank_cons, RealBlock.rank]
      rw [realPositionSign_append ds es i]
      split_ifs with h1 h2 h2
      · rfl
      · omega
      · omega
      · congr 1
        omega

theorem realPositionExponent_append :
    ∀ (ds es : List RealBlock) (i : ℕ),
      GramFormula.realPositionExponent (ds ++ es) i =
        if i < realRank ds then GramFormula.realPositionExponent ds i
        else GramFormula.realPositionExponent es (i - realRank ds)
  | [], es, i => by simp
  | .character d :: ds, es, 0 => by simp [GramFormula.realPositionExponent, RealBlock.rank]
  | .character d :: ds, es, i + 1 => by
      simp only [List.cons_append, GramFormula.realPositionExponent, realRank_cons, RealBlock.rank]
      rw [realPositionExponent_append ds es i]
      split_ifs with h1 h2 h2
      · rfl
      · omega
      · omega
      · congr 1
        omega
  | .induced d :: ds, es, 0 => by simp [GramFormula.realPositionExponent, RealBlock.rank]
  | .induced d :: ds, es, 1 => by
      simp [GramFormula.realPositionExponent, RealBlock.rank]
      intro h
      omega
  | .induced d :: ds, es, i + 2 => by
      simp only [List.cons_append, GramFormula.realPositionExponent, realRank_cons, RealBlock.rank]
      rw [realPositionExponent_append ds es i]
      split_ifs with h1 h2 h2
      · rfl
      · omega
      · omega
      · congr 1
        omega

theorem realInducedBlockAt_append :
    ∀ (ds es : List RealBlock) (i : ℕ),
      realInducedBlockAt (ds ++ es) i =
        if i < realRank ds then realInducedBlockAt ds i
        else realInducedBlockAt es (i - realRank ds)
  | [], es, i => by simp
  | .character d :: ds, es, 0 => by simp [realInducedBlockAt, RealBlock.rank]
  | .character d :: ds, es, i + 1 => by
      simp only [List.cons_append, realInducedBlockAt, realRank_cons, RealBlock.rank]
      rw [realInducedBlockAt_append ds es i]
      split_ifs with h1 h2 h2
      · rfl
      · omega
      · omega
      · congr 1
        omega
  | .induced d :: ds, es, 0 => by simp [realInducedBlockAt, RealBlock.rank]
  | .induced d :: ds, es, 1 => by
      simp [realInducedBlockAt, RealBlock.rank]
      intro h
      omega
  | .induced d :: ds, es, i + 2 => by
      simp only [List.cons_append, realInducedBlockAt, realRank_cons, RealBlock.rank]
      rw [realInducedBlockAt_append ds es i]
      split_ifs with h1 h2 h2
      · rfl
      · omega
      · omega
      · congr 1
        omega

/-! ## Induction blocks -/

/-- At the first position `p` of an induction block of weight `m` and exponent `t`, the signs
are `|m| + 1 (mod 2)` and `0` and the exponents are `t + |m|/2` and `t - |m|/2`. -/
theorem realPosition_of_realInducedBlockAt :
    ∀ {ds : List RealBlock} {p : ℕ} {d : ComplexCharacterData},
      realInducedBlockAt ds p = some d →
        realPositionSign ds p = ⟨(d.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩ ∧
        realPositionSign ds (p + 1) = 0 ∧
        GramFormula.realPositionExponent ds p = d.exponent + (d.weight.natAbs : ℂ) / 2 ∧
        GramFormula.realPositionExponent ds (p + 1) = d.exponent - (d.weight.natAbs : ℂ) / 2
  | [], _, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: _, 0, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: ds, p + 1, _, h => by
      simp only [realInducedBlockAt] at h
      simpa only [realPositionSign, GramFormula.realPositionExponent] using
        realPosition_of_realInducedBlockAt (ds := ds) h
  | .induced _ :: ds, 0, _, h => by
      simp only [realInducedBlockAt, Option.some.injEq] at h
      subst h
      simp [realPositionSign, GramFormula.realPositionExponent]
  | .induced _ :: _, 1, _, h => by simp [realInducedBlockAt] at h
  | .induced _ :: ds, p + 2, _, h => by
      simp only [realInducedBlockAt] at h
      simpa only [realPositionSign, GramFormula.realPositionExponent] using
        realPosition_of_realInducedBlockAt (ds := ds) h

/-! ## The `ρ`-shifted exponents -/

/-- The `ρ`-shifted exponents `tᵢ + (N - 1)/2 - i` of the position characters of `ds`. -/
def shiftedExponent (N : ℕ) (ds : List RealBlock) (i : Fin N) : ℂ :=
  GramFormula.realPositionExponent ds i + ((N : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)

/-- The signs of the position characters of `ds` at the positions `0, …, N - 1`. -/
def positionSign (N : ℕ) (ds : List RealBlock) (i : Fin N) : Fin 2 :=
  realPositionSign ds i

theorem expo_shiftedExponent (N : ℕ) (ds : List RealBlock) (i : Fin N) :
    expo (shiftedExponent N ds) i = GramFormula.realPositionExponent ds i := by
  unfold expo shiftedExponent
  ring

/-- The characters of the principal series of a Frobenius function with exponents
`shiftedExponent N ds` and signs `positionSign N ds` are the position characters of `ds`. -/
theorem posChar_shiftedExponent (N : ℕ) (ds : List RealBlock) (i : Fin N) :
    posChar (shiftedExponent N ds) (positionSign N ds) i = realPositionCharacter ds i := by
  funext x
  rw [posChar_apply, expo_shiftedExponent, realPositionCharacter_eq_charFun]
  rfl

/-- A principal series only depends on its characters at the positions `0, …, N - 1`. -/
theorem principalSeries_congr {N : ℕ} {χ χ' : ℕ → ℝˣ → ℂ} (h : ∀ i : Fin N, χ i = χ' i) :
    principalSeries ℝ N χ = principalSeries ℝ N χ' := by
  have hc : ∀ a : Fin N → ℝˣ, principalSeriesCharacter ℝ N χ a =
      principalSeriesCharacter ℝ N χ' a := fun a => by
    unfold principalSeriesCharacter
    exact Finset.prod_congr rfl fun i _ => by rw [h i]
  ext f
  simp only [mem_principalSeries_iff, hc]

theorem principalSeries_posChar_shiftedExponent (N : ℕ) (ds : List RealBlock) :
    principalSeries ℝ N (posChar (shiftedExponent N ds) (positionSign N ds)) =
      principalSeries ℝ N (realPositionCharacter ds) :=
  principalSeries_congr fun i => posChar_shiftedExponent N ds i

/-- Functions of the principal series of the position characters of `ds` satisfy
`IsExpEquivariant` with the exponents `shiftedExponent N ds`. -/
theorem isExpEquivariant_shiftedExponent {N : ℕ} {ds : List RealBlock}
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : f ∈ principalSeries ℝ N (realPositionCharacter ds)) :
    IsExpEquivariant (shiftedExponent N ds) f :=
  isExpEquivariant_of_mem_principalSeries (τ := fun i => GramFormula.realPositionExponent ds i)
    (fun i x => realPositionCharacter_exp ds i x) hf

/-- At an induction block of weight `m` at `p`, the shifted exponents differ by `|m| + 1`. -/
theorem shiftedExponent_sub_of_realInducedBlockAt {N : ℕ} {ds : List RealBlock} {p : ℕ}
    {d : ComplexCharacterData} (hd : realInducedBlockAt ds p = some d) (h : p + 1 < N) :
    shiftedExponent N ds (ia h) - shiftedExponent N ds (ib h) = (d.weight.natAbs : ℂ) + 1 := by
  obtain ⟨-, -, h1, h2⟩ := realPosition_of_realInducedBlockAt hd
  unfold shiftedExponent
  simp only [ia, ib, h1, h2]
  push_cast
  ring

/-! ## Membership in the standard module -/

/-- If `(-1)^k = (-1)^((m + 1) mod 2)` in `ℂ`, then `k + m + 1` is even. -/
theorem even_of_neg_one_zpow_eq {k : ℤ} {m : ℕ} (h : (-1 : ℂ) ^ k = (-1 : ℂ) ^ ((m + 1) % 2)) :
    Even (k + m + 1) := by
  by_contra hne
  have hodd : Odd (k + m + 1) := Int.not_even_iff_odd.mp hne
  have h1 : (-1 : ℂ) ^ (k + m + 1) = -1 := hodd.neg_one_zpow
  rw [← neg_one_pow_eq_pow_mod_two] at h
  rw [add_assoc, zpow_add₀ (by norm_num), h, show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow] at h1
  norm_num at h1

/-- A function of the principal series of the position characters of `ds` lies in the
standard module of `ds` when the Fourier conditions at the induction blocks hold on `O(N)`.
The coefficients of the window `|k| < |m|`, `k ≡ |m| + 1 (mod 2)` vanish everywhere by
`blockFourierCoefficient_window_eq_zero`, since the shifted exponents differ by `|m| + 1`; the
others vanish by parity. -/
theorem mem_realStandardModule_of_unitaryCompact {N : ℕ} {ds : List RealBlock}
    (hN : realRank ds = N)
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : f ∈ principalSeries ℝ N (realPositionCharacter ds))
    (hK : ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt ds p = some d →
      ∀ k : ℤ, |k| < |d.weight| → ∀ g ∈ unitaryCompact ℝ N, blockFourierCoefficient N p k f g = 0) :
    f ∈ realStandardModule N ds := by
  refine (mem_realStandardModule_iff N ds f).mpr ⟨hf, fun p d hd k hk g => ?_⟩
  have h : p + 1 < N := hN ▸ realInducedBlockAt_lt hd
  have habs : |d.weight| = (d.weight.natAbs : ℤ) := Int.abs_eq_natAbs d.weight
  by_cases hpar :
      (-1 : ℂ) ^ k = realPositionCharacter ds p (-1) * realPositionCharacter ds (p + 1) (-1)
  · have hw : k ∈ window d.weight.natAbs := by
      obtain ⟨hs1, hs2, -, -⟩ := realPosition_of_realInducedBlockAt hd
      rw [realPositionCharacter_neg_one, realPositionCharacter_neg_one, hs1, hs2] at hpar
      simp only [Fin.val_zero, pow_zero, mul_one] at hpar
      exact mem_window.mpr ⟨habs ▸ hk, even_of_neg_one_zpow_eq hpar⟩
    refine blockFourierCoefficient_window_eq_zero h hf.1 (isExpEquivariant_shiftedExponent hf)
      (shiftedExponent_sub_of_realInducedBlockAt hd h) (fun k' hk' j hj => ?_) g k hw
    exact hK p d hd j (habs ▸ (mem_window.mp hj).1) k' hk'
  · exact blockFourierCoefficient_eq_zero_of_parity h (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one ds)
      hf hpar g

/-! ## Lists `pre ++ ws ++ post` -/

section Middle

variable (pre ws post : List RealBlock)

/-- Inside the middle list `ws` of `pre ++ ws ++ post`, the position signs are those of `ws`. -/
theorem realPositionSign_mid {j : ℕ} (hj : j < realRank ws) :
    realPositionSign (pre ++ ws ++ post) (realRank pre + j) = realPositionSign ws j := by
  rw [List.append_assoc, realPositionSign_append, realPositionSign_append]
  split_ifs <;> first | omega | (congr 1; omega)

/-- Inside the middle list `ws` of `pre ++ ws ++ post`, the position exponents are those of
`ws`. -/
theorem realPositionExponent_mid {j : ℕ} (hj : j < realRank ws) :
    GramFormula.realPositionExponent (pre ++ ws ++ post) (realRank pre + j) = GramFormula.realPositionExponent ws j := by
  rw [List.append_assoc, realPositionExponent_append, realPositionExponent_append]
  split_ifs <;> first | omega | (congr 1; omega)

/-- Inside the middle list `ws` of `pre ++ ws ++ post`, the induction blocks are those of
`ws`. -/
theorem realInducedBlockAt_mid {j : ℕ} (hj : j < realRank ws) :
    realInducedBlockAt (pre ++ ws ++ post) (realRank pre + j) = realInducedBlockAt ws j := by
  rw [List.append_assoc, realInducedBlockAt_append, realInducedBlockAt_append]
  split_ifs <;> first | omega | (congr 1; omega)

theorem realPositionCharacter_mid {j : ℕ} (hj : j < realRank ws) :
    realPositionCharacter (pre ++ ws ++ post) (realRank pre + j) = realPositionCharacter ws j := by
  funext x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun,
    realPositionSign_mid pre ws post hj, realPositionExponent_mid pre ws post hj]

variable {pre ws post} {ws' : List RealBlock}

/-- Outside the middle lists, `pre ++ ws ++ post` and `pre ++ ws' ++ post` have the same
position signs when `ws` and `ws'` have the same rank. -/
theorem realPositionSign_of_not_mid (h : realRank ws = realRank ws') {i : ℕ}
    (hi : i < realRank pre ∨ realRank pre + realRank ws ≤ i) :
    realPositionSign (pre ++ ws ++ post) i = realPositionSign (pre ++ ws' ++ post) i := by
  rw [List.append_assoc, List.append_assoc, realPositionSign_append, realPositionSign_append pre,
    realPositionSign_append ws, realPositionSign_append ws']
  split_ifs <;> first | rfl | omega | (congr 1; omega)

theorem realPositionExponent_of_not_mid (h : realRank ws = realRank ws') {i : ℕ}
    (hi : i < realRank pre ∨ realRank pre + realRank ws ≤ i) :
    GramFormula.realPositionExponent (pre ++ ws ++ post) i = GramFormula.realPositionExponent (pre ++ ws' ++ post) i := by
  rw [List.append_assoc, List.append_assoc, realPositionExponent_append,
    realPositionExponent_append pre, realPositionExponent_append ws,
    realPositionExponent_append ws']
  split_ifs <;> first | rfl | omega | (congr 1; omega)

theorem realInducedBlockAt_of_not_mid (h : realRank ws = realRank ws') {i : ℕ}
    (hi : i < realRank pre ∨ realRank pre + realRank ws ≤ i) :
    realInducedBlockAt (pre ++ ws ++ post) i = realInducedBlockAt (pre ++ ws' ++ post) i := by
  rw [List.append_assoc, List.append_assoc, realInducedBlockAt_append,
    realInducedBlockAt_append pre, realInducedBlockAt_append ws,
    realInducedBlockAt_append ws']
  split_ifs <;> first | rfl | omega | (congr 1; omega)

theorem realPositionCharacter_of_not_mid (h : realRank ws = realRank ws') {i : ℕ}
    (hi : i < realRank pre ∨ realRank pre + realRank ws ≤ i) :
    realPositionCharacter (pre ++ ws ++ post) i = realPositionCharacter (pre ++ ws' ++ post) i := by
  funext x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun,
    realPositionSign_of_not_mid h hi, realPositionExponent_of_not_mid h hi]

/-- An induction block of `pre ++ ws ++ post` starting at a position `i < realRank pre` ends
before `realRank pre`. -/
theorem lt_of_realInducedBlockAt_of_lt {i : ℕ} {d : ComplexCharacterData}
    (hd : realInducedBlockAt (pre ++ ws ++ post) i = some d) (hi : i < realRank pre) :
    i + 1 < realRank pre := by
  rw [List.append_assoc, realInducedBlockAt_append] at hd
  simp only [hi, ↓reduceIte] at hd
  exact realInducedBlockAt_lt hd

end Middle

/-- A list of real blocks of rank two has no induction block starting at position `1`. -/
theorem realInducedBlockAt_one_of_realRank_eq_two {ws : List RealBlock} (h : realRank ws = 2) :
    realInducedBlockAt ws 1 = none := by
  match ws, h with
  | [], h => simp [realRank] at h
  | .induced _ :: _, _ => rfl
  | [.character _], h => simp [RealBlock.rank] at h
  | .character _ :: .character _ :: _, _ => rfl
  | .character _ :: .induced _ :: _, h =>
      simp only [realRank_cons, RealBlock.rank] at h
      omega

end RealBlockPosition

end Langlands.Archimedean
