import Langlands.LocalFactor.ArchimedeanPresentation
import Mathlib.Data.List.Perm.Basic

/-! # Pair factors of archimedean Weil-group presentations

Tensor products of the Library's archimedean Weil-group blocks, written again as lists of
blocks: characters of `ℝˣ` and `ℂˣ` multiply, a character of `ℝˣ` twists an induced block by its
composite with the norm, and two induced blocks give two induced blocks. The pair `L`- and
`ε`-factors of two presentations are the published factors of the presentation of their
tensor product. The identification of these block lists with the actual tensor product
representations is explained in the Markdown and is not proved here.
-/

noncomputable section

namespace Langlands.LocalFactor.Archimedean

open Langlands.Weil.Archimedean

/-- Complex conjugation on `W_ℂ = ℂˣ`, as a continuous homomorphism. -/
def complexConjugation : ComplexWeil →ₜ* ComplexWeil where
  toMonoidHom := Units.map (starRingEnd ℂ).toMonoidHom
  continuous_toFun := Units.continuous_iff.mpr
    ⟨Complex.continuous_conj.comp Units.continuous_val,
      Complex.continuous_conj.comp Units.continuous_coe_inv⟩

@[simp]
theorem coe_complexConjugation (z : ComplexWeil) :
    ((complexConjugation z : ComplexWeil) : ℂ) = (starRingEnd ℂ) (z : ℂ) :=
  rfl

private theorem sign_pow_mul {s : ℂ} (hs : s ^ 2 = 1) (a b : Fin 2) :
    s ^ a.val * s ^ b.val = s ^ (a + b).val := by
  rw [← pow_add, Fin.val_add, ← Nat.mod_add_div (a.val + b.val) 2, pow_add, pow_mul, hs,
    one_pow, mul_one, Nat.mod_add_div]

private theorem real_sign_sq (x : ℝˣ) :
    ((((x : ℝ) / |(x : ℝ)| : ℝ) : ℂ)) ^ 2 = 1 := by
  have hx : (x : ℝ) ≠ 0 := x.ne_zero
  have habs : |(x : ℝ)| ≠ 0 := abs_ne_zero.mpr hx
  have h : ((x : ℝ) / |(x : ℝ)|) ^ 2 = 1 := by
    rw [div_pow, sq_abs, div_self (pow_ne_zero 2 hx)]
  exact_mod_cast h

namespace RealCharacterData

/-- The product of two real characters, with added parities and exponents. -/
def mul (c d : RealCharacterData) : RealCharacterData where
  character := c.character * d.character
  parity := c.parity + d.parity
  exponent := c.exponent + d.exponent
  character_eq x := by
    have hx : ((|(x : ℝ)| : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast abs_ne_zero.mpr x.ne_zero
    rw [ContinuousMonoidHom.mul_apply, Units.val_mul, c.character_eq, d.character_eq,
      Complex.cpow_add _ _ hx, ← sign_pow_mul (real_sign_sq x)]
    ring

end RealCharacterData

private theorem complex_unit_ne_zero (z : ComplexWeil) : ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ≠ 0 :=
  div_ne_zero z.ne_zero (by exact_mod_cast (norm_ne_zero_iff.mpr z.ne_zero))

private theorem complex_norm_ne_zero (z : ComplexWeil) : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast norm_ne_zero_iff.mpr z.ne_zero

namespace ComplexCharacterData

/-- The product of two complex characters, with added weights and exponents. -/
def mul (c d : ComplexCharacterData) : ComplexCharacterData where
  character := c.character * d.character
  weight := c.weight + d.weight
  exponent := c.exponent + d.exponent
  character_eq z := by
    rw [ContinuousMonoidHom.mul_apply, Units.val_mul, c.character_eq, d.character_eq,
      zpow_add₀ (complex_unit_ne_zero z), mul_add, Complex.cpow_add _ _ (complex_norm_ne_zero z)]
    ring

/-- The conjugate character `z ↦ χ(z̄)`, with negated weight. -/
def conj (d : ComplexCharacterData) : ComplexCharacterData where
  character := d.character.comp complexConjugation
  weight := -d.weight
  exponent := d.exponent
  character_eq z := by
    have hn : ‖(starRingEnd ℂ) (z : ℂ)‖ = ‖(z : ℂ)‖ := Complex.norm_conj _
    have hu : (starRingEnd ℂ) (z : ℂ) / (‖(z : ℂ)‖ : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ))⁻¹ := by
      have hz : (z : ℂ) ≠ 0 := z.ne_zero
      have hnz : (‖(z : ℂ)‖ : ℂ) ≠ 0 := complex_norm_ne_zero z
      rw [inv_div, div_eq_div_iff hnz hz, Complex.conj_mul']
      ring
    change ((d.character (complexConjugation z) : ℂˣ) : ℂ) = _
    rw [d.character_eq, coe_complexConjugation, hn, hu, inv_zpow', zpow_neg]

/-- The twist of a complex character by a real character composed with the norm
`z ↦ z z̄`. -/
def twistReal (d : ComplexCharacterData) (c : RealCharacterData) : ComplexCharacterData where
  character := d.character * c.character.comp complexNorm
  weight := d.weight
  exponent := d.exponent + c.exponent
  character_eq z := by
    have hpos : 0 < Complex.normSq (z : ℂ) := Complex.normSq_pos.mpr z.ne_zero
    have hsign : ((((complexNorm z : ℝˣ) : ℝ) / |((complexNorm z : ℝˣ) : ℝ)| : ℝ) : ℂ) = 1 := by
      rw [complexNorm_apply, abs_of_pos hpos, div_self hpos.ne']
      simp
    have habs : (((|((complexNorm z : ℝˣ) : ℝ)| : ℝ) : ℂ)) ^ c.exponent =
        ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ (2 * c.exponent) := by
      rw [complexNorm_apply, abs_of_pos hpos, Complex.normSq_eq_norm_sq]
      have hn : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
      have h1 : (((‖(z : ℂ)‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hn 2).ne'
      rw [Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero (complex_norm_ne_zero z),
        ← Complex.ofReal_log (pow_pos hn 2).le, ← Complex.ofReal_log hn.le, Real.log_pow]
      push_cast
      ring_nf
    rw [ContinuousMonoidHom.mul_apply, Units.val_mul, d.character_eq,
      ContinuousMonoidHom.comp_toFun, c.character_eq, hsign, habs, one_pow, one_mul, mul_add,
      Complex.cpow_add _ _ (complex_norm_ne_zero z)]
    ring

end ComplexCharacterData

namespace RealBlock

/-- The tensor product of two real blocks, as a list of real blocks: characters multiply, a
character twists an induced block by its composite with the norm, and
`Ind(μ) ⊗ Ind(ν) = Ind(μν) ⊕ Ind(μν̄)`. -/
def tensor : RealBlock → RealBlock → List RealBlock
  | character c, character d => [character (c.mul d)]
  | character c, induced d => [induced (d.twistReal c)]
  | induced d, character c => [induced (d.twistReal c)]
  | induced d, induced e => [induced (d.mul e), induced (d.mul e.conj)]

/-- The tensor product has the product rank. -/
theorem realRank_tensor (x y : RealBlock) : realRank (x.tensor y) = x.rank * y.rank := by
  cases x <;> cases y <;> simp [tensor, rank, realRank]

end RealBlock

/-- The blocks of the tensor product of two real presentations: the tensor products of all
pairs of blocks. -/
def realPairBlocks (xs ys : List RealBlock) : List RealBlock :=
  xs.flatMap fun x => ys.flatMap x.tensor

theorem realRank_append (xs ys : List RealBlock) :
    realRank (xs ++ ys) = realRank xs + realRank ys := by
  simp [realRank, List.map_append, List.sum_append]

theorem realRank_flatMap_tensor (x : RealBlock) (ys : List RealBlock) :
    realRank (ys.flatMap x.tensor) = x.rank * realRank ys := by
  induction ys with
  | nil => simp [realRank]
  | cons y ys ih =>
    rw [List.flatMap_cons, realRank_append, ih, RealBlock.realRank_tensor, realRank_cons,
      mul_add]

/-- The pair presentation has the product rank. -/
theorem realRank_realPairBlocks (xs ys : List RealBlock) :
    realRank (realPairBlocks xs ys) = realRank xs * realRank ys := by
  induction xs with
  | nil => simp [realPairBlocks, realRank]
  | cons x xs ih =>
    rw [realPairBlocks, List.flatMap_cons, ← realPairBlocks, realRank_append,
      realRank_flatMap_tensor, ih, realRank_cons, add_mul]

/-- Permuting either presentation permutes the blocks of the pair presentation. -/
theorem realPairBlocks_perm {xs xs' ys ys' : List RealBlock} (hx : xs.Perm xs')
    (hy : ys.Perm ys') : (realPairBlocks xs ys).Perm (realPairBlocks xs' ys') :=
  (List.Perm.flatMap_left xs fun x _ => hy.flatMap_right x.tensor).trans
    (hx.flatMap_right _)

/-- The pair `L`-factor of two real presentations: the `L`-factor of their tensor product. -/
def realPairLFactor (xs ys : List RealBlock) : ReciprocalEntire :=
  realLFactor (realPairBlocks xs ys)

/-- The standard pair `ε`-factor of two real presentations. -/
def realPairStandardEpsilon (xs ys : List RealBlock) : ℂˣ :=
  realStandardEpsilon (realPairBlocks xs ys)

/-- The pair `ε`-factor of two real presentations for the twisted additive character and the
scaled measure of the published `realEpsilon`. -/
def realPairEpsilon (xs ys : List RealBlock) (a : ℝˣ) (c : NNReal) (hc : 0 < c) (s : ℂ) :
    ℂˣ :=
  realEpsilon (realPairBlocks xs ys) a c hc s

/-- The real pair `L`-factor does not depend on the order of the blocks. -/
theorem realPairLFactor_perm {xs xs' ys ys' : List RealBlock} (hx : xs.Perm xs')
    (hy : ys.Perm ys') : realPairLFactor xs ys = realPairLFactor xs' ys' :=
  realLFactor_perm (realPairBlocks_perm hx hy)

/-- The real pair `ε`-factor does not depend on the order of the blocks. -/
theorem realPairEpsilon_perm {xs xs' ys ys' : List RealBlock} (hx : xs.Perm xs')
    (hy : ys.Perm ys') (a : ℝˣ) (c : NNReal) (hc : 0 < c) (s : ℂ) :
    realPairEpsilon xs ys a c hc s = realPairEpsilon xs' ys' a c hc s :=
  realEpsilon_perm a c hc s (realPairBlocks_perm hx hy)

/-- The blocks of the tensor product of two complex presentations: all products of their
characters. -/
def complexPairBlocks (xs ys : List ComplexCharacterData) : List ComplexCharacterData :=
  xs.flatMap fun x => ys.map x.mul

theorem length_complexPairBlocks (xs ys : List ComplexCharacterData) :
    (complexPairBlocks xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [complexPairBlocks]
  | cons x xs ih =>
    rw [complexPairBlocks, List.flatMap_cons, ← complexPairBlocks, List.length_append, ih,
      List.length_map, List.length_cons, add_mul, one_mul, add_comm]

/-- The pair `L`-factor of two complex presentations. -/
def complexPairLFactor (xs ys : List ComplexCharacterData) : ReciprocalEntire :=
  complexLFactor (complexPairBlocks xs ys)

/-- The standard pair `ε`-factor of two complex presentations. -/
def complexPairStandardEpsilon (xs ys : List ComplexCharacterData) : ℂˣ :=
  complexStandardEpsilon (complexPairBlocks xs ys)

/-- The pair `ε`-factor of two complex presentations for the twisted additive character and
the scaled measure of the published `complexEpsilon`. -/
def complexPairEpsilon (xs ys : List ComplexCharacterData) (a : ℂˣ) (c : NNReal) (hc : 0 < c)
    (s : ℂ) : ℂˣ :=
  complexEpsilon (complexPairBlocks xs ys) a c hc s

/-- Permuting either presentation permutes the blocks of the complex pair presentation. -/
theorem complexPairBlocks_perm {xs xs' ys ys' : List ComplexCharacterData} (hx : xs.Perm xs')
    (hy : ys.Perm ys') : (complexPairBlocks xs ys).Perm (complexPairBlocks xs' ys') :=
  (List.Perm.flatMap_left xs fun x _ => hy.map x.mul).trans (hx.flatMap_right _)

/-- The complex pair `L`-factor does not depend on the order of the blocks. -/
theorem complexPairLFactor_perm {xs xs' ys ys' : List ComplexCharacterData}
    (hx : xs.Perm xs') (hy : ys.Perm ys') : complexPairLFactor xs ys = complexPairLFactor xs' ys' :=
  complexLFactor_perm (complexPairBlocks_perm hx hy)

/-- The complex pair `ε`-factor does not depend on the order of the blocks. -/
theorem complexPairEpsilon_perm {xs xs' ys ys' : List ComplexCharacterData}
    (hx : xs.Perm xs') (hy : ys.Perm ys') (a : ℂˣ) (c : NNReal) (hc : 0 < c) (s : ℂ) :
    complexPairEpsilon xs ys a c hc s = complexPairEpsilon xs' ys' a c hc s :=
  complexEpsilon_perm a c hc s (complexPairBlocks_perm hx hy)

end Langlands.LocalFactor.Archimedean
