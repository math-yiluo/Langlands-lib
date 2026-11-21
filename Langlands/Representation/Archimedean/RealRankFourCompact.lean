import Langlands.Representation.Archimedean.RealRankFourMatrices
import Langlands.Representation.Archimedean.Kostant.RealTransfer
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Langlands.Representation.Archimedean.RealKTypeTransport
import Langlands.Representation.Archimedean.RealStandardNontrivialProof

/-!
# Compact polynomial for the two-block real rank-four standard module

A sign average of a power of a two-row minor produces a compact highest-weight
vector for the two positive-weight blocks of equal weight.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealRankFourCompact

open Matrix Complex GramFormula RealGramFunction RealRankFourMatrices RealBlockRotation
  RealBlockFourierFinite
open Langlands.LocalFactor.Archimedean
open scoped BigOperators TensorProduct ContDiff Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

private abbrev Plane (A : Type*) := Matrix (Fin 4) (Fin 2) A

private def row {A : Type*} [CommRing A] (Y : Plane A) (p q : Fin 4) (z : A)
    (l : Fin 2) : A := Y p l + z * Y q l

private def minor {A : Type*} [CommRing A] (Y : Plane A) (u v : A) : A :=
  row Y 0 1 u 0 * row Y 2 3 v 1 - row Y 0 1 u 1 * row Y 2 3 v 0

private def signMode {A : Type*} [Neg A] (i : A) (e : Fin 2) : A :=
  if e = 0 then i else -i

private def minorSum {A : Type*} [CommRing A] (Y : Plane A) (i : A) (m : ℕ) : A :=
  ∑ e : Fin 2, ∑ f : Fin 2, minor Y (signMode i e) (signMode i f) ^ m

private abbrev Poly := MvPolynomial (Fin 4 × Fin 4) ℂ

private def polynomial (m : ℕ) : Poly :=
  minorSum (Matrix.of (fun i j => MvPolynomial.X (i, j)) * highestPlane (MvPolynomial.C I))
    (MvPolynomial.C I) m

private theorem map_plane {A B : Type*} [Ring A] [Ring B] (f : A →+* B) (i : A) :
    (highestPlane i).map f = highestPlane (f i) := by
  ext j k
  fin_cases j <;> fin_cases k <;> simp [highestPlane]

private theorem eval_polynomial (m : ℕ) (Y : MatC) :
    MvPolynomial.eval (fun ij => Y ij.1 ij.2) (polynomial m) =
      minorSum (Y * highestPlane I) I m := by
  unfold polynomial minorSum
  simp only [map_sum, map_pow]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  congr 1
  let h : Poly →+* ℂ := MvPolynomial.eval (fun ij => Y ij.1 ij.2)
  have hm : (Matrix.of (fun j k => MvPolynomial.X (j, k)) * highestPlane (MvPolynomial.C I)).map h =
      Y * highestPlane I := by
    rw [Matrix.map_mul, map_plane, show h (MvPolynomial.C I) = I from MvPolynomial.eval_C _]
    congr 1
    ext j k
    exact MvPolynomial.eval_X _
  change h (minor _ _ _) = _
  have hm' : ∀ j k, h (((Matrix.of (fun j k => MvPolynomial.X (j, k)) *
      highestPlane (MvPolynomial.C I)) : Plane Poly) j k) = (Y * highestPlane I) j k :=
    fun j k => congrArg (fun M : Plane ℂ => M j k) hm
  simp only [minor, row, signMode, map_sub, map_add, map_mul, hm', apply_ite, map_neg, h,
    MvPolynomial.eval_C]

def pair (d₁ d₂ : ComplexCharacterData) : List RealBlock := [.induced d₁, .induced d₂]

theorem realRank_pair (d₁ d₂ : ComplexCharacterData) : realRank (pair d₁ d₂) = 4 := rfl

private def witnessFunction (d₁ d₂ : ComplexCharacterData) : Langlands.GeneralLinear 4 ℝ → ℂ :=
  gramFunction (shiftedExponent 4 (realPositionExponent (pair d₁ d₂)))
    (polynomial (d₁.weight.natAbs + 1))

def castMatrix (M : MatR) : MatC := M.map Complex.ofRealHom

private theorem witnessFunction_compact {d₁ d₂ : ComplexCharacterData}
    {k : Langlands.GeneralLinear 4 ℝ} (hk : k ∈ unitaryCompact ℝ 4) :
    witnessFunction d₁ d₂ k =
      minorSum (castMatrix (k : MatR) * highestPlane I) I (d₁.weight.natAbs + 1) := by
  unfold witnessFunction
  rw [gramFunction_eq_extension]
  let u : Matrix.unitaryGroup (Fin 4) ℝ := ⟨(k : MatR), hk⟩
  have hu : Unitary.toUnits u = k := Units.ext rfl
  rw [← hu, PrincipalSeriesExtension.extension_unitary, orthogonalEval]
  exact eval_polynomial _ (castMatrix (k : MatR))

private def signed {A : Type*} [CommRing A] (s : Fin 4 → A) {k : Type*}
    (Y : Matrix (Fin 4) k A) : Matrix (Fin 4) k A :=
  Matrix.of (fun i j => s i * Y i j)

private theorem signed_mul (s : Fin 4 → ℂ) (Y : MatC) :
    signed s Y * highestPlane I = signed s (Y * highestPlane I) := by
  ext j k
  simp only [Matrix.mul_apply, signed, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _

private theorem minor_signed (s : Fin 4 → ℂ) (hs : ∀ i, s i * s i = 1)
    (Y : Plane ℂ) (u v : ℂ) :
    minor (signed s Y) u v = s 0 * s 2 * minor Y (s 0 * s 1 * u) (s 2 * s 3 * v) := by
  have hr (p q : Fin 4) (z : ℂ) (j : Fin 2) :
      row (signed s Y) p q z j = s p * row Y p q (s p * s q * z) j := by
    simp only [row, signed, Matrix.of_apply, mul_add]
    congr 1
    rw [show s p * (s p * s q * z * Y q j) = (s p * s p) * (z * (s q * Y q j)) by ring,
      hs, one_mul]
  simp only [minor, hr]
  ring

private theorem minorSum_signed (s : Fin 4 → ℂ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (Y : Plane ℂ) (m : ℕ) :
    minorSum (signed s Y) I m = (s 0 * s 2) ^ m * minorSum Y I m := by
  have hs₂ (i : Fin 4) : s i * s i = 1 := by
    rcases hs i with h | h <;> simp [h]
  have hflip (i j : Fin 4) : s i * s j = 1 ∨ s i * s j = -1 := by
    rcases hs i with hi | hi <;> rcases hs j with hj | hj <;> simp [hi, hj]
  simp only [minorSum, minor_signed s hs₂, mul_pow, ← Finset.mul_sum]
  congr 1
  rcases hflip 0 1 with h₁ | h₁ <;> rcases hflip 2 3 with h₂ | h₂ <;>
    simp only [Fin.sum_univ_two, signMode, h₁, h₂, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false,
      one_mul, neg_one_mul, neg_neg] <;> abel

private theorem witnessFunction_parity (d₁ d₂ : ComplexCharacterData)
    (hweight : d₁.weight.natAbs = d₂.weight.natAbs) :
    HasSignParity (realPositionCharacter (pair d₁ d₂)) (polynomial (d₁.weight.natAbs + 1)) := by
  intro a Y
  let s : Fin 4 → ℂ := fun i => (signReal (a i) : ℝ)
  let M : MatC := Matrix.of (fun i j => Y (i, j))
  have hY : (fun ij : Fin 4 × Fin 4 => ((signReal (a ij.1) : ℝ) : ℂ) * Y ij) =
      (fun ij => (signed s M) ij.1 ij.2) := funext fun ⟨_, _⟩ => rfl
  rw [hY, eval_polynomial, show Y = (fun ij => M ij.1 ij.2) from funext fun ⟨_, _⟩ => rfl,
    eval_polynomial, signed_mul, minorSum_signed]
  · congr 1
    simp only [Fin.prod_univ_four, pair, realPositionCharacter,
      RealStandardNontrivial.realInducedFirstCharacter_signUnit,
      RealStandardNontrivial.realInducedSecondCharacter_signUnit, ← hweight, mul_one, mul_pow]
    rfl
  · intro j
    rcases RealStandardNontrivial.signReal_eq_one_or (a j) with h | h <;> simp [s, h]

private theorem witnessFunction_one_ne_zero (d₁ d₂ : ComplexCharacterData) :
    witnessFunction d₁ d₂ 1 ≠ 0 := by
  rw [witnessFunction_compact (Subgroup.one_mem _)]
  change minorSum (castMatrix (1 : MatR) * highestPlane I) I _ ≠ 0
  rw [show castMatrix (1 : MatR) = 1 from Complex.ofRealHom.mapMatrix.map_one, Matrix.one_mul]
  simp only [minorSum, Fin.sum_univ_two, signMode, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false]
  have h₁ : minor (highestPlane I) I I = 4 := by
    norm_num [minor, row, highestPlane, ← pow_two, I_sq]
  have h₂ : minor (highestPlane I) I (-I) = 0 := by
    norm_num [minor, row, highestPlane, ← pow_two, I_sq]
  have h₃ : minor (highestPlane I) (-I) I = 0 := by
    norm_num [minor, row, highestPlane, ← pow_two, I_sq]
  have h₄ : minor (highestPlane I) (-I) (-I) = 0 := by
    norm_num [minor, row, highestPlane, ← pow_two, I_sq]
  rw [h₁, h₂, h₃, h₄, zero_pow (Nat.succ_ne_zero _)]
  simp

private theorem castMatrix_mul (X Y : MatR) :
    castMatrix (X * Y) = castMatrix X * castMatrix Y := Matrix.map_mul

private def rotationPosition (lower : Bool) : ℕ := if lower then 2 else 0

private def rotation (lower : Bool) (c s : ℂ) : MatC :=
  if lower then !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, c, -s; 0, 0, s, c]
  else !![c, -s, 0, 0; s, c, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private theorem castMatrix_blockRotation (lower : Bool) (θ : ℝ) :
    castMatrix (blockRotation 4 (rotationPosition lower) θ : MatR) =
      rotation lower (Real.cos θ) (Real.sin θ) := by
  have hp : rotationPosition lower + 1 < 4 := by cases lower <;> decide
  rw [blockRotation_val_eq hp, RealStandardNontrivial.rotMatrix_eq]
  ext i j
  cases lower <;> fin_cases i <;> fin_cases j <;>
    norm_num [castMatrix, rotation, rotationPosition, ia, ib, Matrix.single_apply,
      Matrix.one_apply, Fin.ext_iff, sub_mul, add_mul]

private theorem minor_rotation (lower : Bool) (c s u v : ℂ) (Y : Plane ℂ)
    (hu : u ^ 2 = -1) (hv : v ^ 2 = -1) :
    minor (rotation lower c s * Y) u v =
      (c + (if lower then v else u) * s) * minor Y u v := by
  have hUpper (j : Fin 2) : row (rotation false c s * Y) 0 1 u j =
      (c + u * s) * row Y 0 1 u j := by
    simp [row, rotation, Matrix.mul_apply, Fin.sum_univ_four]
    linear_combination (-s * Y 1 j) * hu
  have hLower (j : Fin 2) : row (rotation true c s * Y) 2 3 v j =
      (c + v * s) * row Y 2 3 v j := by
    simp [row, rotation, Matrix.mul_apply, Fin.sum_univ_four]
    linear_combination (-s * Y 3 j) * hv
  cases lower
  · have hOther (j : Fin 2) : row (rotation false c s * Y) 2 3 v j = row Y 2 3 v j := by
      simp [row, rotation, Matrix.mul_apply, Fin.sum_univ_four]
    simp [minor, hUpper, hOther]
    ring
  · have hOther (j : Fin 2) : row (rotation true c s * Y) 0 1 u j = row Y 0 1 u j := by
      simp [row, rotation, Matrix.mul_apply, Fin.sum_univ_four]
    simp [minor, hLower, hOther]
    ring

private def frequency (m : ℕ) (e : Fin 2) : ℤ := if e = 0 then m else -(m : ℤ)

private theorem abs_frequency (m : ℕ) (e : Fin 2) : |frequency m e| = (m : ℤ) := by
  unfold frequency
  split <;> simp

private theorem signMode_sq (e : Fin 2) : signMode I e ^ 2 = -1 := by
  unfold signMode
  split <;> simp [I_sq]

private theorem rotationFactor_pow (m : ℕ) (e : Fin 2) (θ : ℝ) :
    ((Real.cos θ : ℂ) + signMode I e * (Real.sin θ : ℂ)) ^ m =
      expMode (frequency m e) θ := by
  have h (x : ℝ) : ((Real.cos x : ℂ) + I * (Real.sin x : ℂ)) ^ m =
      expMode (m : ℤ) x := by
    rw [ofReal_cos, ofReal_sin, mul_comm I, ← exp_mul_I, ← exp_nat_mul, expMode]
    push_cast
    rw [mul_assoc]
  fin_cases e
  · exact h θ
  · change ((Real.cos θ : ℂ) + (-I) * (Real.sin θ : ℂ)) ^ m = expMode (-(m : ℤ)) θ
    simpa only [Real.cos_neg, Real.sin_neg, ofReal_neg, mul_neg, neg_mul, expMode, Int.cast_neg,
      Int.cast_natCast] using h (-θ)

private theorem witnessFunction_rotation (d₁ d₂ : ComplexCharacterData) (lower : Bool)
    {k : Langlands.GeneralLinear 4 ℝ} (hk : k ∈ unitaryCompact ℝ 4) (θ : ℝ) :
    witnessFunction d₁ d₂ (blockRotation 4 (rotationPosition lower) θ * k) =
      ∑ e : Fin 2, ∑ f : Fin 2,
        minor (castMatrix (k : MatR) * highestPlane I) (signMode I e) (signMode I f) ^
          (d₁.weight.natAbs + 1) *
        expMode (frequency (d₁.weight.natAbs + 1) (if lower then f else e)) θ := by
  rw [witnessFunction_compact (mul_mem (blockRotation_mem_unitaryCompact _ _ _) hk),
    Units.val_mul, castMatrix_mul, castMatrix_blockRotation, Matrix.mul_assoc]
  unfold minorSum
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  rw [minor_rotation lower _ _ _ _ _ (signMode_sq e) (signMode_sq f), mul_pow, mul_comm]
  congr 1
  rw [show (if lower then signMode I f else signMode I e) =
      signMode I (if lower then f else e) by cases lower <;> rfl, rotationFactor_pow]

private theorem coeff_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℂ) (j : ℤ)
    (hc : ∀ i ∈ s, Continuous (F i)) :
    coeff j (∑ i ∈ s, F i) = ∑ i ∈ s, coeff j (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeff_zero_fun]
  | @insert i s hi ih =>
    have hs : ∀ k ∈ s, Continuous (F k) :=
      fun k hk => hc k (Finset.mem_insert_of_mem hk)
    have hs' : Continuous (∑ k ∈ s, F k) := by
      change Continuous (fun θ => (∑ k ∈ s, F k) θ)
      simp_rw [Finset.sum_apply]
      exact continuous_finsetSum _ hs
    rw [Finset.sum_insert hi, coeff_add (hc i (Finset.mem_insert_self i s)) hs',
      ih hs, Finset.sum_insert hi]

private theorem witnessFunction_fourier (d₁ d₂ : ComplexCharacterData) (lower : Bool)
    (j : ℤ) (hj : |j| < (d₁.weight.natAbs + 1 : ℤ))
    {k : Langlands.GeneralLinear 4 ℝ} (hk : k ∈ unitaryCompact ℝ 4) :
    blockFourierCoefficient 4 (rotationPosition lower) j (witnessFunction d₁ d₂) k = 0 := by
  let F (e f : Fin 2) : ℝ → ℂ :=
    minor (castMatrix (k : MatR) * highestPlane I) (signMode I e) (signMode I f) ^
      (d₁.weight.natAbs + 1) • expMode (frequency (d₁.weight.natAbs + 1) (if lower then f else e))
  have hc (e f : Fin 2) : Continuous (F e f) := (continuous_expMode _).const_smul _
  have hF : (fun θ => witnessFunction d₁ d₂ (blockRotation 4 (rotationPosition lower) θ * k)) =
      ∑ e : Fin 2, ∑ f : Fin 2, F e f := by
    funext θ
    rw [witnessFunction_rotation d₁ d₂ lower hk]
    simp only [Finset.sum_apply, F, Pi.smul_apply, smul_eq_mul]
  have hc' (e : Fin 2) : Continuous (∑ f, F e f) := by
    change Continuous (fun θ => (∑ f, F e f) θ)
    simp_rw [Finset.sum_apply]
    exact continuous_finsetSum _ (fun f _ => hc e f)
  rw [blockFourierCoefficient_eq_coeff, hF, coeff_sum _ _ _ (fun e _ => hc' e)]
  apply Finset.sum_eq_zero
  intro e _
  rw [coeff_sum _ _ _ (fun f _ => hc e f)]
  apply Finset.sum_eq_zero
  intro f _
  dsimp only [F]
  have hne : frequency (d₁.weight.natAbs + 1) (if lower then f else e) ≠ j := by
    intro h
    rw [← h, abs_frequency] at hj
    omega
  simp [coeff_smul, coeff_expMode, hne]

private theorem witnessFunction_mem (d₁ d₂ : ComplexCharacterData)
    (hweight : d₁.weight.natAbs = d₂.weight.natAbs) :
    witnessFunction d₁ d₂ ∈ kFiniteFunctions (realStandardModule 4 (pair d₁ d₂))
      (unitaryCompact ℝ 4) := by
  have hK := gramFunction_mem_kFiniteFunctions (realPositionExponent (pair d₁ d₂))
    (realPositionCharacter_eq_signUnit_mul (pair d₁ d₂)) (witnessFunction_parity d₁ d₂ hweight)
  refine ⟨RealKTypeTransport.mem_realStandardModule_of_unitaryCompact (realRank_pair d₁ d₂) hK.1 ?_, hK.2⟩
  intro p d hd j hj k hk
  have hp := realInducedBlockAt_lt hd
  rw [realRank_pair] at hp
  have hp' : p < 3 := by omega
  interval_cases p
  · change some d₁ = some d at hd
    have := Option.some.inj hd
    subst d
    apply witnessFunction_fourier d₁ d₂ false j _ hk
    rw [Int.abs_eq_natAbs d₁.weight] at hj
    omega
  · simp [pair, realInducedBlockAt] at hd
  · change some d₂ = some d at hd
    have := Option.some.inj hd
    subst d
    apply witnessFunction_fourier d₁ d₂ true j _ hk
    rw [Int.abs_eq_natAbs d₂.weight, ← hweight] at hj
    omega

private def minorTangent (Y Z : Plane ℂ) (u v : ℂ) : ℂ :=
  (row Z 0 1 u 0 * row Y 2 3 v 1 + row Y 0 1 u 0 * row Z 2 3 v 1) -
    (row Z 0 1 u 1 * row Y 2 3 v 0 + row Y 0 1 u 1 * row Z 2 3 v 0)

private theorem minorTangent_right_mul (Y : Plane ℂ) (D : Matrix (Fin 2) (Fin 2) ℂ) (u v : ℂ) :
    minorTangent Y (Y * D) u v = D.trace * minor Y u v := by
  simp only [minorTangent, minor, row, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two]
  ring

private def tangent (m : ℕ) (Y : Plane ℂ) : Plane ℂ →ₗ[ℂ] ℂ where
  toFun Z := ∑ e : Fin 2, ∑ f : Fin 2,
    ((m : ℂ) + 1) * minor Y (signMode I e) (signMode I f) ^ m *
      minorTangent Y Z (signMode I e) (signMode I f)
  map_add' Z W := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
    simp only [minorTangent, row, Matrix.add_apply]
    ring
  map_smul' z Z := by
    simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
    simp only [minorTangent, row, Matrix.smul_apply, smul_eq_mul]
    ring

private theorem tangent_right_mul (m : ℕ) (Y : Plane ℂ) (D : Matrix (Fin 2) (Fin 2) ℂ) :
    tangent m Y (Y * D) = (((m : ℂ) + 1) * D.trace) * minorSum Y I (m + 1) := by
  simp only [tangent, LinearMap.coe_mk, AddHom.coe_mk, minorTangent_right_mul, minorSum,
    Finset.mul_sum, pow_succ]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  ring

private theorem hasDerivAt_minorSum {γ : ℝ → Plane ℂ} {Z : Plane ℂ}
    (hγ : ∀ i j, HasDerivAt (fun t => γ t i j) (Z i j) 0) (m : ℕ) :
    HasDerivAt (fun t => minorSum (γ t) I (m + 1)) (tangent m (γ 0) Z) 0 := by
  simp only [minorSum, tangent, LinearMap.coe_mk, AddHom.coe_mk]
  apply HasDerivAt.fun_sum
  intro e _
  apply HasDerivAt.fun_sum
  intro f _
  have hrow (p q : Fin 4) (z : ℂ) (j : Fin 2) :
      HasDerivAt (fun t => row (γ t) p q z j) (row Z p q z j) 0 :=
    (hγ p j).add ((hγ q j).const_mul z)
  let u := signMode I e
  let v := signMode I f
  have hminor : HasDerivAt (fun t => minor (γ t) u v) (minorTangent (γ 0) Z u v) 0 :=
    ((hrow 0 1 u 0).mul (hrow 2 3 v 1)).sub ((hrow 0 1 u 1).mul (hrow 2 3 v 0))
  simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using hminor.fun_pow (m + 1)

/-- The compact-finite carrier of the two-block standard module. -/
abbrev Standard (d₁ d₂ : ComplexCharacterData) :=
  kFiniteFunctions (realStandardModule 4 (pair d₁ d₂)) (unitaryCompact ℝ 4)

/-- The standard Lie action transported to complex matrices. -/
def action (d₁ d₂ : ComplexCharacterData) : MatC →ₗ⁅ℂ⁆ Module.End ℂ (Standard d₁ d₂) :=
  (realStandardLie 4 (pair d₁ d₂)).comp ((Kostant.toGL 4).symm.toLieHom.comp
    { toFun := fun X _ => X
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      map_lie' := fun {_ _} => rfl })

theorem action_castMatrix (d₁ d₂ : ComplexCharacterData) (X : MatR) :
    action d₁ d₂ (castMatrix X) = realStandardLie 4 (pair d₁ d₂) (1 ⊗ₜ X) := by
  have h : (Kostant.toGL 4) (1 ⊗ₜ X) = fun _ : Unit => castMatrix X := by
    funext u
    rw [Kostant.toGL_tmul, one_smul]
    rfl
  change realStandardLie 4 (pair d₁ d₂) ((Kostant.toGL 4).symm (fun _ => castMatrix X)) = _
  rw [← h, LieEquiv.symm_apply_apply]

private def witness (d₁ d₂ : ComplexCharacterData)
    (hweight : d₁.weight.natAbs = d₂.weight.natAbs) : Standard d₁ d₂ :=
  ⟨witnessFunction d₁ d₂, witnessFunction_mem d₁ d₂ hweight⟩

theorem castMatrix_basisR (b : Fin 4 × Fin 4) : castMatrix (basisR b) = basisC b :=
  ofReal_basisR b

private theorem eval_action_skew (d₁ d₂ : ComplexCharacterData)
    (hweight : d₁.weight.natAbs = d₂.weight.natAbs)
    {k : Langlands.GeneralLinear 4 ℝ} (hk : k ∈ unitaryCompact ℝ 4)
    (X : MatR) (hX : Xᵀ = -X) :
    ((action d₁ d₂ (castMatrix X) (witness d₁ d₂ hweight) : Standard d₁ d₂) :
        Langlands.GeneralLinear 4 ℝ → ℂ) k =
      tangent d₁.weight.natAbs (castMatrix (k : MatR) * highestPlane I)
        (castMatrix (k : MatR) * (castMatrix X * highestPlane I)) := by
  rw [action_castMatrix, realStandardLie_one_tmul_apply_coe]
  change rightDerivative (matrixModel ℝ 4) X (witnessFunction d₁ d₂) k = _
  have hF := contMDiff_gramFunction
    (shiftedExponent 4 (realPositionExponent (pair d₁ d₂))) (polynomial (d₁.weight.natAbs + 1))
  have h₁ := hasDerivAt_mul_matrixExpUnit_smul (hF.of_le (by norm_num)) k X
  let γ : ℝ → Plane ℂ := fun t =>
    castMatrix ((k : MatR) * NormedSpace.exp (t • X)) * highestPlane I
  have hγ₀ : γ 0 = castMatrix (k : MatR) * highestPlane I := by
    simp [γ]
  have hγ (i : Fin 4) (j : Fin 2) :
      HasDerivAt (fun t => γ t i j)
        ((castMatrix (k : MatR) * (castMatrix X * highestPlane I)) i j) 0 := by
    have h := (RealPrincipalSeriesDuality.hasDerivAt_exp_smul_zero X).const_mul (k : MatR)
    rw [← Matrix.mul_assoc, ← castMatrix_mul]
    change HasDerivAt (fun t => ∑ q : Fin 4, (((k : MatR) *
      NormedSpace.exp (t • X)) i q : ℝ) * highestPlane I q j)
      (∑ q : Fin 4, (((k : MatR) * X) i q : ℝ) * highestPlane I q j) 0
    exact HasDerivAt.fun_sum fun q _ =>
      ((RealPrincipalSeriesDuality.hasDerivAt_entry h i q).ofReal_comp).mul_const _
  have h₂ := hasDerivAt_minorSum hγ d₁.weight.natAbs
  rw [hγ₀] at h₂
  have hm (t : ℝ) : matrixExpUnit 4 (t • X) ∈ unitaryCompact ℝ 4 := by
    change NormedSpace.exp (t • X) ∈ Matrix.unitaryGroup (Fin 4) ℝ
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    apply skewAdjoint.smul_mem
    rwa [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  have hfun : (fun t => witnessFunction d₁ d₂ (k * matrixExpUnit 4 (t • X))) =
      (fun t => minorSum (γ t) I (d₁.weight.natAbs + 1)) := by
    funext t
    rw [witnessFunction_compact (mul_mem hk (hm t))]
    rfl
  change HasDerivAt (fun t => witnessFunction d₁ d₂ (k * matrixExpUnit 4 (t • X)))
    (rightDerivative (matrixModel ℝ 4) X (witnessFunction d₁ d₂) k) 0 at h₁
  rw [hfun] at h₁
  exact h₁.unique h₂

private theorem eval_action_topK (d₁ d₂ : ComplexCharacterData)
    (hweight : d₁.weight.natAbs = d₂.weight.natAbs)
    {k : Langlands.GeneralLinear 4 ℝ} (hk : k ∈ unitaryCompact ℝ 4) (i : Fin 3) :
    ((action d₁ d₂ (K i) (witness d₁ d₂ hweight) : Standard d₁ d₂) :
        Langlands.GeneralLinear 4 ℝ → ℂ) k =
      tangent d₁.weight.natAbs (castMatrix (k : MatR) * highestPlane I)
        (castMatrix (k : MatR) * (K i * highestPlane I)) := by
  simpa only [castMatrix_basisR] using
    eval_action_skew d₁ d₂ hweight hk (basisR (i.succ, 0)) (basisR_K_transpose i)

private theorem eval_action_rightK (d₁ d₂ : ComplexCharacterData)
    (hweight : d₁.weight.natAbs = d₂.weight.natAbs)
    {k : Langlands.GeneralLinear 4 ℝ} (hk : k ∈ unitaryCompact ℝ 4) (i : Fin 3) :
    ((action d₁ d₂ (R i) (witness d₁ d₂ hweight) : Standard d₁ d₂) :
        Langlands.GeneralLinear 4 ℝ → ℂ) k =
      tangent d₁.weight.natAbs (castMatrix (k : MatR) * highestPlane I)
        (castMatrix (k : MatR) * (R i * highestPlane I)) := by
  simpa only [castMatrix_basisR] using
    eval_action_skew d₁ d₂ hweight hk (basisR (0, i.succ)) (basisR_R_transpose i)

private theorem standard_ext_on_compact {d₁ d₂ : ComplexCharacterData} {v w : Standard d₁ d₂}
    (h : ∀ k ∈ unitaryCompact ℝ 4, (v : Langlands.GeneralLinear 4 ℝ → ℂ) k =
      (w : Langlands.GeneralLinear 4 ℝ → ℂ) k) : v = w :=
  Subtype.ext (eq_of_eqOn_unitaryCompact_of_mem_principalSeries v.2.1.1 w.2.1.1 h)

/-- The two-block standard module contains a highest vector of left compact
spin `abs(weight)+1` and right compact spin zero whose value at `1` is nonzero. -/
theorem exists_highest_vector (d₁ d₂ : ComplexCharacterData)
    (hweight : d₁.weight.natAbs = d₂.weight.natAbs) :
    ∃ v : Standard d₁ d₂, (v : Langlands.GeneralLinear 4 ℝ → ℂ) 1 ≠ 0 ∧
      action d₁ d₂ raising v = 0 ∧
      action d₁ d₂ (K 2) v = (((d₁.weight.natAbs : ℂ) + 1) * I) • v ∧
      ∀ j : Fin 3, action d₁ d₂ (R j) v = 0 := by
  refine ⟨witness d₁ d₂ hweight, witnessFunction_one_ne_zero d₁ d₂, ?_, ?_, ?_⟩
  · apply standard_ext_on_compact
    intro k hk
    rw [raising, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
    change _ - I * _ = 0
    rw [eval_action_topK d₁ d₂ hweight hk, eval_action_topK d₁ d₂ hweight hk,
      K_mul_highestPlane.1, Matrix.mul_smul, map_smul, smul_eq_mul, sub_self]
  · apply standard_ext_on_compact
    intro k hk
    change _ = (((d₁.weight.natAbs : ℂ) + 1) * I) * witnessFunction d₁ d₂ k
    rw [eval_action_topK d₁ d₂ hweight hk, witnessFunction_compact hk]
    have hscalar : (I / 2) • highestPlane I =
        highestPlane I * ((I / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
      rw [Matrix.mul_smul, Matrix.mul_one]
    rw [K_mul_highestPlane.2, hscalar, ← Matrix.mul_assoc, tangent_right_mul]
    simp
  · intro j
    apply standard_ext_on_compact
    intro k hk
    change _ = (0 : ℂ)
    rw [eval_action_rightK d₁ d₂ hweight hk, R_mul_highestPlane, ← Matrix.mul_assoc,
      tangent_right_mul]
    have hTrace : (rightPlaneAction j).trace = 0 := by
      fin_cases j <;> simp [rightPlaneAction, Matrix.trace_fin_two]
      ring
    rw [hTrace, mul_zero, zero_mul]

end Langlands.Archimedean.RealRankFourCompact
