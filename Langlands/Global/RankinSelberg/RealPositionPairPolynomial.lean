import Langlands.Global.RankinSelberg.RealBlockParameters
import Langlands.Global.RankinSelberg.RealPrincipalSeriesFactors
import Langlands.LocalFactor.RealPairLFactorNormalization

/-! # The polynomial relating the real block and position pair factors -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealBlockParameters

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.LocalFactor.Archimedean.RealGammaReflection (positionParity)
open RealPrincipalSeries (expand)

local notation "denR" => gammaReal.denominator
local notation "denC" => gammaComplex.denominator

private abbrev pairDen (xs ys : List RealBlock) : ℂ → ℂ := (realPairLFactor xs ys).denominator

/-- The polynomial given by a list of shifts, with the scale from the Gamma recurrence. -/
def shiftProduct (shifts : List ℂ) (z : ℂ) : ℂ :=
  (shifts.map fun b => (z + b) / (2 * (Real.pi : ℂ))).prod

private theorem shiftProduct_append (l m : List ℂ) (z : ℂ) :
    shiftProduct (l ++ m) z = shiftProduct l z * shiftProduct m z := by
  simp [shiftProduct]

private theorem shiftProduct_translate (l : List ℂ) (z a : ℂ) :
    shiftProduct (l.map fun b => a + b) z = shiftProduct l (z + a) := by
  simp only [shiftProduct, List.map_map, Function.comp_def, add_assoc]

private theorem denR_step (z : ℂ) : denR z = (z / (2 * (Real.pi : ℂ))) * denR (z + 2) := by
  change (Complex.Gammaℝ z)⁻¹ = (z / _) * (Complex.Gammaℝ (z + 2))⁻¹
  by_cases hz : z = 0
  · subst z
    have h : Complex.Gammaℝ 0 = 0 := Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩
    simp [h]
  · rw [Complex.Gammaℝ_add_two hz, div_div, mul_div_assoc, mul_inv, mul_comm (Complex.Gammaℝ z)⁻¹,
      ← mul_assoc, mul_inv_cancel₀ (div_ne_zero hz
        (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))), one_mul]

private theorem denC_step (z : ℂ) : denC z = (z / (2 * (Real.pi : ℂ))) * denC (z + 1) := by
  change (Complex.Gammaℂ z)⁻¹ = (z / _) * (Complex.Gammaℂ (z + 1))⁻¹
  by_cases hz : z = 0
  · subst z
    simp [Complex.Gammaℂ_def]
  · rw [Complex.Gammaℂ_add_one hz, div_div, mul_div_assoc, mul_inv, mul_comm (Complex.Gammaℂ z)⁻¹,
      ← mul_assoc, mul_inv_cancel₀ (div_ne_zero hz
        (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))), one_mul]

private theorem exists_stepFactors (D : ℂ → ℂ) (a : ℂ)
    (hD : ∀ z, D z = (z / (2 * (Real.pi : ℂ))) * D (z + a)) (n : ℕ) :
    ∃ l : List ℂ, ∀ z, D z = shiftProduct l z * D (z + a * n) := by
  induction n with
  | zero => exact ⟨[], fun z => by simp [shiftProduct]⟩
  | succ n ih =>
      obtain ⟨l, hl⟩ := ih
      refine ⟨(l.map fun b => a + b).cons 0, fun z => ?_⟩
      have hcons : shiftProduct ((l.map fun b => a + b).cons 0) z =
          (z / (2 * (Real.pi : ℂ))) * shiftProduct l (z + a) := by
        change ((z + 0) / _) * shiftProduct (l.map fun b => a + b) z = _
        rw [add_zero, shiftProduct_translate]
      rw [hcons, show z + a * ((n + 1 : ℕ) : ℂ) = z + a + a * (n : ℂ) by push_cast; ring,
        mul_assoc, ← hl (z + a), ← hD z]

private theorem denC_eq_denR (z : ℂ) : denC z = denR z * denR (z + 1) := by
  change (Complex.Gammaℂ z)⁻¹ = (Complex.Gammaℝ z)⁻¹ * (Complex.Gammaℝ (z + 1))⁻¹
  rw [← mul_inv, Complex.Gammaℝ_mul_Gammaℝ_add_one]

private theorem denR_parities (p : Fin 2) (z : ℂ) :
    denR (z + (p.val : ℂ)) * denR (z + ((p + 1).val : ℂ)) = denC z := by
  have h : p = 0 ∨ p = 1 := by omega
  rcases h with rfl | rfl
  · simpa only [zero_add, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, add_zero]
      using (denC_eq_denR z).symm
  · simp only [show (1 + 1 : Fin 2) = 0 by decide, Fin.val_zero, Fin.val_one, Nat.cast_zero,
      Nat.cast_one, add_zero, denC_eq_denR]
    exact mul_comm _ _

private theorem mixed_factors (k : ℕ) (q : Fin 2) :
    ∃ l : List ℂ, ∀ z : ℂ,
      denR (z + (k : ℂ) / 2 + ((positionParity k + q).val : ℂ)) *
        denR (z - (k : ℂ) / 2 + (q.val : ℂ)) =
      shiftProduct l z * denC (z + (k : ℂ) / 2) := by
  let p := positionParity k + q
  have hq := q.isLt
  have hp : p.val = (k + 1 + q.val) % 2 := by
    simp only [p, positionParity, Fin.val_add, Fin.val_ofNat]
    omega
  have h : k + (p + 1).val = q.val + 2 * ((k + (p + 1).val - q.val) / 2) := by
    rw [Fin.val_add, Fin.val_one, hp]
    omega
  let n := (k + (p + 1).val - q.val) / 2
  have hcast : (k : ℂ) + ((p + 1).val : ℂ) = (q.val : ℂ) + 2 * (n : ℂ) := by
    exact_mod_cast h
  obtain ⟨l, hl⟩ := exists_stepFactors denR 2 denR_step n
  refine ⟨l.map fun b => (-(k : ℂ) / 2 + (q.val : ℂ)) + b, fun z => ?_⟩
  change denR (z + (k : ℂ) / 2 + (p.val : ℂ)) * _ = _
  rw [shiftProduct_translate, ← show z - (k : ℂ) / 2 + (q.val : ℂ) =
      z + (-(k : ℂ) / 2 + (q.val : ℂ)) by ring, hl (z - (k : ℂ) / 2 + (q.val : ℂ)),
    show z - (k : ℂ) / 2 + (q.val : ℂ) + 2 * (n : ℂ) =
      z + (k : ℂ) / 2 + ((p + 1).val : ℂ) by linear_combination -hcast,
    mul_left_comm, denR_parities]

private theorem sumDiff_natAbs (k l : ℤ) (z : ℂ) :
    denC (z + ((k + l).natAbs : ℂ) / 2) * denC (z + ((k + -l).natAbs : ℂ) / 2) =
      denC (z + ((k.natAbs : ℂ) + l.natAbs) / 2) *
      denC (z + ((max k.natAbs l.natAbs - min k.natAbs l.natAbs : ℕ) : ℂ) / 2) := by
  have h :
      ((k + l).natAbs = k.natAbs + l.natAbs ∧
        (k + -l).natAbs = max k.natAbs l.natAbs - min k.natAbs l.natAbs) ∨
      ((k + -l).natAbs = k.natAbs + l.natAbs ∧
        (k + l).natAbs = max k.natAbs l.natAbs - min k.natAbs l.natAbs) := by
    rcases le_total k.natAbs l.natAbs with h | h
    · rw [max_eq_right h, min_eq_left h]
      omega
    · rw [max_eq_left h, min_eq_right h]
      omega
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂, Nat.cast_add]
  · rw [h₁, h₂, Nat.cast_add, mul_comm]

private theorem induced_factors (k l : ℤ) :
    ∃ p : List ℂ, ∀ z : ℂ,
      denC (z + ((k.natAbs : ℂ) + l.natAbs) / 2) *
        denC (z + ((l.natAbs : ℂ) - k.natAbs) / 2) =
      shiftProduct p z *
        (denC (z + ((k + l).natAbs : ℂ) / 2) *
          denC (z + ((k + -l).natAbs : ℂ) / 2)) := by
  by_cases h : k.natAbs ≤ l.natAbs
  · refine ⟨[], fun z => ?_⟩
    rw [sumDiff_natAbs, max_eq_right h, min_eq_left h, Nat.cast_sub h]
    simp [shiftProduct]
  · have h' := le_of_not_ge h
    let n := k.natAbs - l.natAbs
    let a : ℂ := ((l.natAbs : ℂ) - k.natAbs) / 2
    obtain ⟨p, hp⟩ := exists_stepFactors denC 1 denC_step n
    refine ⟨p.map fun b => a + b, fun z => ?_⟩
    have ha : a + (n : ℂ) = (n : ℂ) / 2 := by
      dsimp [a, n]
      rw [Nat.cast_sub h']
      ring
    rw [shiftProduct_translate, sumDiff_natAbs, max_eq_left h', min_eq_right h']
    change _ * denC (z + a) = _
    rw [hp (z + a), one_mul, add_assoc z a, ha, mul_left_comm]

private theorem expand_character_singleton (p : Fin 2) (u : ℂ) :
    expand [blockOfParams (.inl p) u] = [blockOfParams (.inl p) u] := rfl

private theorem expand_induced_singleton (k : ℤ) (u : ℂ) :
    expand [blockOfParams (.inr k) u] =
      [blockOfParams (.inl (positionParity k.natAbs)) (u + (k.natAbs : ℂ) / 2),
        blockOfParams (.inl 0) (u - (k.natAbs : ℂ) / 2)] := rfl

private theorem pairDen_append_left (xs ys zs : List RealBlock) (s : ℂ) :
    pairDen (xs ++ ys) zs s = pairDen xs zs s * pairDen ys zs s := by
  rw [pairDen, realPairLFactor, realPairBlocks, List.flatMap_append, realLFactor_append]
  rfl

private theorem pairDen_append_right (xs ys zs : List RealBlock) (s : ℂ) :
    pairDen xs (ys ++ zs) s = pairDen xs ys s * pairDen xs zs s := by
  simp only [pairDen]
  rw [realPairLFactor_comm xs, ← pairDen, pairDen_append_left]
  simp only [pairDen, realPairLFactor_comm ys xs, realPairLFactor_comm zs xs]

private theorem pairDen_singletons (x y : RealBlock) (s : ℂ) :
    pairDen [x] [y] s = (realLFactor (x.tensor y)).denominator s := by
  simp [pairDen, realPairLFactor, realPairBlocks]

private theorem exists_firstSlot_factors (p q : Shape) :
    ∃ l : List ℂ, ∀ u v s : ℂ,
      pairDen (expand [blockOfParams p u]) [blockOfParams q v] s =
        shiftProduct l (s + (u + v)) * pairDen [blockOfParams p u] [blockOfParams q v] s := by
  cases p with
  | inl p => exact ⟨[], fun u v s => by simp [expand_character_singleton, shiftProduct]⟩
  | inr k =>
      cases q with
      | inl q =>
          obtain ⟨l, hl⟩ := mixed_factors k.natAbs q
          refine ⟨l, fun u v s => ?_⟩
          rw [expand_induced_singleton, show ∀ x y : RealBlock, [x, y] = [x] ++ [y] from
            fun _ _ => rfl, pairDen_append_left]
          simp only [pairDen_singletons, blockOfParams, RealBlock.tensor, realLFactor_singleton,
            RealBlock.lFactor_character, RealBlock.lFactor_induced,
            ReciprocalEntire.denominator_shift, RealCharacterData.mul,
            ComplexCharacterData.twistReal, charData_parity, charData_exponent,
            Langlands.Archimedean.characterOfParams_weight,
            Langlands.Archimedean.characterOfParams_exponent, zero_add]
          have h := hl (s + (u + v))
          ring_nf at h ⊢
          exact h
      | inr l =>
          obtain ⟨p, hp⟩ := induced_factors k l
          refine ⟨p, fun u v s => ?_⟩
          rw [expand_induced_singleton, show ∀ x y : RealBlock, [x, y] = [x] ++ [y] from
            fun _ _ => rfl, pairDen_append_left]
          simp only [pairDen_singletons, blockOfParams, RealBlock.tensor, denominator_realLFactor,
            List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            RealBlock.lFactor_induced, ReciprocalEntire.denominator_shift,
            ComplexCharacterData.twistReal, ComplexCharacterData.mul, ComplexCharacterData.conj,
            charData_exponent, Langlands.Archimedean.characterOfParams_weight,
            Langlands.Archimedean.characterOfParams_exponent]
          have h := hp (s + (u + v))
          ring_nf at h ⊢
          exact h

private theorem pairDen_comm (xs ys : List RealBlock) (s : ℂ) :
    pairDen xs ys s = pairDen ys xs s := by
  rw [pairDen, realPairLFactor_comm]

private theorem exists_position_factors (p q : Shape) :
    ∃ l : List ℂ, ∀ u v s : ℂ,
      pairDen (expand [blockOfParams p u]) (expand [blockOfParams q v]) s =
        shiftProduct l (s + (u + v)) * pairDen [blockOfParams p u] [blockOfParams q v] s := by
  cases p with
  | inl p =>
      obtain ⟨l, hl⟩ := exists_firstSlot_factors q (.inl p)
      refine ⟨l, fun u v s => ?_⟩
      rw [expand_character_singleton, pairDen_comm, hl v u, add_comm v u, pairDen_comm]
  | inr k =>
      let a : ℂ := (k.natAbs : ℂ) / 2
      obtain ⟨l, hl⟩ := exists_firstSlot_factors (.inr k) q
      obtain ⟨m, hm⟩ := exists_firstSlot_factors q (.inl (positionParity k.natAbs))
      obtain ⟨n, hn⟩ := exists_firstSlot_factors q (.inl 0)
      refine ⟨(m.map fun b => a + b) ++ (n.map fun b => -a + b) ++ l, fun u v s => ?_⟩
      let x := blockOfParams (.inl (positionParity k.natAbs)) (u + a)
      let y := blockOfParams (.inl 0) (u - a)
      have hxy : expand [blockOfParams (.inr k) u] = [x] ++ [y] := rfl
      rw [hxy, pairDen_append_left, pairDen_comm [x], pairDen_comm [y], hm v (u + a), hn v (u - a),
        pairDen_comm [blockOfParams q v] [x], pairDen_comm [blockOfParams q v] [y],
        shiftProduct_append, shiftProduct_append, shiftProduct_translate, shiftProduct_translate,
        show s + (v + (u + a)) = s + (u + v) + a by ring,
        show s + (v + (u - a)) = s + (u + v) + -a by ring, mul_mul_mul_comm,
        ← pairDen_append_left, ← hxy, hl u v]
      simp only [mul_assoc]

private theorem pairDen_flatMap_left {A : Type*} (xs : List A) (f : A → List RealBlock)
    (ys : List RealBlock) (s : ℂ) :
    pairDen (xs.flatMap f) ys s = (xs.map fun x => pairDen (f x) ys s).prod := by
  induction xs with
  | nil => simp [pairDen, realPairLFactor, realPairBlocks, ReciprocalEntire.one]
  | cons x xs ih =>
      simp only [List.flatMap_cons, pairDen_append_left, ih, List.map_cons, List.prod_cons]

private theorem pairDen_flatMap_right {B : Type*} (xs : List RealBlock) (ys : List B)
    (g : B → List RealBlock) (s : ℂ) :
    pairDen xs (ys.flatMap g) s = (ys.map fun y => pairDen xs (g y) s).prod := by
  rw [pairDen_comm, pairDen_flatMap_left]
  exact congrArg List.prod (List.map_congr_left fun y _ => pairDen_comm (g y) xs s)

private theorem pairDen_ofFn_flatMap {n m : ℕ} (x : Fin n → List RealBlock)
    (y : Fin m → List RealBlock) (s : ℂ) :
    pairDen ((List.ofFn id).flatMap x) ((List.ofFn id).flatMap y) s =
      ∏ i, ∏ j, pairDen (x i) (y j) s := by
  rw [pairDen_flatMap_left]
  simp only [pairDen_flatMap_right, List.map_ofFn, List.prod_ofFn, Function.comp_apply, id_eq]

private theorem blockList_eq_flatMap {n : ℕ} (sh : Fin n → Shape) (p : Fin n → ℂ) :
    blockList sh p = (List.ofFn id).flatMap (fun i => [blockOfParams (sh i) (p i)]) := by
  rw [← List.map_eq_flatMap, List.map_ofFn]
  rfl

private theorem expand_blockList_eq_flatMap {n : ℕ} (sh : Fin n → Shape) (p : Fin n → ℂ) :
    expand (blockList sh p) = (List.ofFn id).flatMap (fun i => expand [blockOfParams (sh i) (p i)]) := by
  simp only [blockList_eq_flatMap, expand, List.flatMap_assoc]

/-- The reciprocal pair denominator of the position expansion is the true block
denominator times a polynomial in the spectral variable. Its linear factors are
shifted by sums of block exponents, and are otherwise determined by the block shapes. -/
def RealPositionPairPolynomialStatement : Prop :=
  ∃ shifts : Shape → Shape → List ℂ,
    ∀ {n m : ℕ} (sh : Fin n → Shape) (sh' : Fin m → Shape)
      (p : Fin n → ℂ) (q : Fin m → ℂ) (s : ℂ),
      (realPairLFactor (expand (blockList sh p)) (expand (blockList sh' q))).denominator s =
        (∏ i, ∏ j, shiftProduct (shifts (sh i) (sh' j)) (s + (p i + q j))) *
          (realPairLFactor (blockList sh p) (blockList sh' q)).denominator s

theorem realPositionPairPolynomial : RealPositionPairPolynomialStatement := by
  classical
  choose shifts hshifts using exists_position_factors
  refine ⟨shifts, fun sh sh' p q s => ?_⟩
  change pairDen (expand (blockList sh p)) (expand (blockList sh' q)) s =
    _ * pairDen (blockList sh p) (blockList sh' q) s
  rw [expand_blockList_eq_flatMap, expand_blockList_eq_flatMap, pairDen_ofFn_flatMap,
    blockList_eq_flatMap, blockList_eq_flatMap, pairDen_ofFn_flatMap]
  simp only [hshifts, Finset.prod_mul_distrib]

end Langlands.Global.RankinSelbergGlobal.RealBlockParameters
