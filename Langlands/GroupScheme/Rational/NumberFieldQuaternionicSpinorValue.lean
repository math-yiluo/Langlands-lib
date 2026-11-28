import Langlands.GroupScheme.Rational.NumberFieldQuaternionicSpinKernelReduction
import Langlands.GroupScheme.Rational.NumberFieldQuaternionicPureLineValue
import Langlands.GroupScheme.Quaternionic.QuaternionicSkewQuadraticComparison
import Langlands.GroupScheme.Quaternionic.QuaternionicSkewIsometryTransport

/-! # Line similitudes with a prescribed reduced norm class -/

noncomputable section

universe u

open scoped TensorProduct
open NumberField

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open Langlands.CentralSimple

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

section Coordinates

variable {F D : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)

omit [CharZero F] [Algebra.IsCentral F D] in
/-- The scalar extension of the quaternion conjugation is the scalar extension of the
original involution twisted by the alternating unit. -/
theorem baseChange_quaternionConjugation (K : Type u) [Field K] [Algebra F K] (z : K ⊗[F] D) :
    (σ.quaternionConjugation hdim hsym).baseChange K z =
      ((1 : K) ⊗ₜ[F] (σ.quaternionAlternatingUnit hdim hsym : D)) * σ.baseChange K z *
        ((1 : K) ⊗ₜ[F] (σ.quaternionAlternatingUnit hdim hsym : D)⁻¹) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [FirstKindInvolution.map_add, FirstKindInvolution.map_add, hx, hy,
      mul_add, add_mul]
  | tmul r a =>
    rw [FirstKindInvolution.baseChange_tmul, FirstKindInvolution.baseChange_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rfl

omit [CharZero F] [Algebra.IsCentral F D] in
/-- In coordinates over a field extension, the skew row pairing for the canonical
conjugation is the original polar row pairing times the inverse alternating unit. -/
theorem sum_conjugationSkewGram_baseChange {n : ℕ} (q : σ.QuadraticForms (Fin n))
    (K : Type u) [Field K] [Algebra F K] (y : Fin n → K ⊗[F] D) :
    ∑ j, ∑ k, y j * ((1 : K) ⊗ₜ[F] σ.conjugationSkewGram q hdim hsym j k) *
        (σ.quaternionConjugation hdim hsym).baseChange K (y k) =
      (∑ j, ∑ k, y j * ((1 : K) ⊗ₜ[F] σ.polar q j k) * σ.baseChange K (y k)) *
        ((1 : K) ⊗ₜ[F] (σ.quaternionAlternatingUnit hdim hsym : D)⁻¹) := by
  set l : D := (σ.quaternionAlternatingUnit hdim hsym : D)
  have hl0 : l ≠ 0 := (σ.quaternionAlternatingUnit hdim hsym).ne_zero
  have hH (j k : Fin n) : σ.conjugationSkewGram q hdim hsym j k = σ.polar q j k * l⁻¹ := by
    change (σ.polar q * Matrix.scalar (Fin n) l⁻¹) j k = _
    simp only [Matrix.scalar_apply, Matrix.mul_diagonal]
  have hinv : ((1 : K) ⊗ₜ[F] l⁻¹) * ((1 : K) ⊗ₜ[F] l) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hl0]
    rfl
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have hsplit : (1 : K) ⊗ₜ[F] (σ.polar q j k * l⁻¹) =
      ((1 : K) ⊗ₜ[F] σ.polar q j k) * ((1 : K) ⊗ₜ[F] l⁻¹) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [hH, hsplit, baseChange_quaternionConjugation]
  calc y j * ((1 : K) ⊗ₜ[F] σ.polar q j k * (1 : K) ⊗ₜ[F] l⁻¹) *
        ((1 : K) ⊗ₜ[F] l * σ.baseChange K (y k) * (1 : K) ⊗ₜ[F] l⁻¹)
      = y j * ((1 : K) ⊗ₜ[F] σ.polar q j k) * (((1 : K) ⊗ₜ[F] l⁻¹) * ((1 : K) ⊗ₜ[F] l)) *
          σ.baseChange K (y k) * (1 : K) ⊗ₜ[F] l⁻¹ := by noncomm_ring
    _ = _ := by rw [hinv, mul_one]

end Coordinates

section NumberField

variable {F D : Type u} [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)

include hdim hsym in
/-- A nondegenerate quadratic form of rank at least three over the quaternion division algebra
has a vector with nonzero polar self-value. -/
theorem exists_polar_sesqForm_ne_zero {n : ℕ} (hn : 3 ≤ n) (q : σ.QuadraticForms (Fin n))
    (hq : σ.IsNondegenerateQuadratic q) : ∃ x : Fin n → D, σ.sesqForm (σ.polar q) x x ≠ 0 := by
  set τ := σ.quaternionConjugation hdim hsym
  have hH := σ.isAntihermitian_conjugationSkewGram q hdim hsym
  have hu := σ.isUnit_conjugationSkewGram q hdim hsym hq
  have hI : 3 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn
  have hsq1 (v : InfinitePlace F) : IsSquare (algebraMap F v.Completion 1) :=
    ⟨1, by rw [_root_.map_one, mul_one]⟩
  obtain ⟨d, s, c, -, -, hc, hell⟩ := σ.exists_elliptic_mul_conjugation hdim hsym 1 one_ne_zero
    (fun v _ h => absurd (hsq1 v) h)
  obtain ⟨w, c', hw0, hwτ, hwc, hloc⟩ : ∃ (w : D) (c' : F), w ≠ 0 ∧ τ w = -w ∧
      w * w = algebraMap F D c' ∧ ∀ v : InfinitePlace F, v.IsReal →
        ¬ IsSquare (algebraMap F v.Completion c') := by
    by_cases hw : d - τ d = 0
    · have hreal (v : InfinitePlace F) (hv : v.IsReal) : False := by
        have h := hell v hv (hsq1 v)
        have hc0 : c = 0 :=
          (algebraMap F D).injective (by rw [← hc, hw, mul_zero, _root_.map_zero])
        rw [hc0, _root_.map_zero, _root_.map_zero] at h
        exact lt_irrefl _ h
      refine ⟨(KneserThree.Quaternion.ell σ hdim hsym : D), _,
        (KneserThree.Quaternion.ell σ hdim hsym).ne_zero,
        KneserThree.Quaternion.conj_ell σ hdim hsym,
        KneserThree.Quaternion.ell_mul_self (σ := σ) (hdim := hdim) (hsym := hsym),
        fun v hv => (hreal v hv).elim⟩
    · refine ⟨d - τ d, c, hw, by rw [τ.map_sub, τ.apply_apply, neg_sub], hc, fun v hv h => ?_⟩
      obtain ⟨t, ht⟩ := h
      have h' := hell v hv (hsq1 v)
      rw [ht, _root_.map_mul] at h'
      exact absurd h' (not_lt.mpr (mul_self_nonneg _))
  obtain ⟨x, b, hb, hx⟩ := σ.exists_value_on_pureLine_of_real hdim hsym hI hH hu hw0 hwτ hwc
    (fun v hv h => absurd h (hloc v hv))
  refine ⟨x, fun h => ?_⟩
  have h' := σ.sesqForm_conjugationSkewGram hdim hsym q x x
  rw [h, zero_mul, hx] at h'
  exact smul_ne_zero hb hw0 h'

end NumberField

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution

namespace Langlands.GroupScheme

open Quaternionic Langlands.CentralSimple

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Let `a ∈ Fˣ` be a square at every real place where the quaternion algebra stays a division
algebra or the form stays anisotropic. Then there is a similitude `d` of a line of nonzero
hermitian value with `Nrd(d) = a s²` for a unit `s ∈ Fˣ`. -/
theorem numberFieldQuaternionicSpinorValue : NumberFieldQuaternionicSpinorValueStatement.{u} := by
  intro F _ _ D _ _ _ _ hdim σ hsym n _ hn q hq a hreal
  set τ := σ.quaternionConjugation hdim hsym
  set l : D := (σ.quaternionAlternatingUnit hdim hsym : D)
  have hl0 : l ≠ 0 := (σ.quaternionAlternatingUnit hdim hsym).ne_zero
  set P := σ.polar q
  set H := σ.conjugationSkewGram q hdim hsym
  have hH := σ.isAntihermitian_conjugationSkewGram q hdim hsym
  have hu := σ.isUnit_conjugationSkewGram q hdim hsym hq
  have hI : 3 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn
  have hsplit (v : InfinitePlace F) (hv : v.IsReal)
      (hns : ¬ IsSquare (algebraMap F v.Completion (a : F))) :
      (∃ y : v.Completion ⊗[F] D, y ≠ 0 ∧ ¬ IsUnit y) ∧
        ∃ y : Fin n → v.Completion ⊗[F] D, y ≠ 0 ∧
          ∑ j, ∑ k, y j * ((1 : v.Completion) ⊗ₜ[F] H j k) *
            τ.baseChange v.Completion (y k) = 0 := by
    have h := mt (hreal v hv) hns
    simp only [FirstKindInvolution.DivisionOrAnisotropicAt] at h
    push Not at h
    obtain ⟨hy₁, y, hy, hy0⟩ := h
    refine ⟨hy₁, y, hy0, ?_⟩
    rw [σ.sum_conjugationSkewGram_baseChange hdim hsym q, hy, zero_mul]
  obtain ⟨d, s, c, hs0, hd, hc, hell⟩ := σ.exists_elliptic_mul_conjugation hdim hsym (a : F)
    a.ne_zero fun v hv hns => (hsplit v hv hns).1
  have hNrd : reducedNorm F D F ((1 : F) ⊗ₜ[F] d) = (a : F) * s ^ 2 :=
    (algebraMap F D).injective ((σ.quaternionConjugation_norm hdim hsym d).symm.trans hd)
  obtain ⟨t, ht⟩ := KneserThree.Quaternion.add_conj_mem σ hdim hsym d
  have hτd : τ d = algebraMap F D t - d := by
    rw [← ht]
    change τ d = d + τ d - d
    abel
  -- the value line: either `d` is central or the line of `d - τ d`
  obtain ⟨x, hx0, hcomm⟩ : ∃ x : Fin n → D, σ.sesqForm P x x ≠ 0 ∧
      d * τ.sesqForm H x x = τ.sesqForm H x x * d := by
    by_cases hw : d - τ d = 0
    · obtain ⟨x, hx⟩ := σ.exists_polar_sesqForm_ne_zero hdim hsym hn q hq
      refine ⟨x, hx, ?_⟩
      have hdc : d = algebraMap F D (t / 2) := by
        have h2 : algebraMap F D 2 * d = algebraMap F D t := by
          rw [← ht, map_ofNat]
          change 2 * d = d + τ d
          rw [← sub_eq_zero.mp hw, two_mul]
        have hne : algebraMap F D 2 ≠ 0 := (map_ne_zero _).mpr two_ne_zero
        calc d = (algebraMap F D 2)⁻¹ * (algebraMap F D 2 * d) := by
              rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
          _ = algebraMap F D (t / 2) := by
              rw [h2, ← map_inv₀, ← _root_.map_mul, div_eq_inv_mul]
      rw [hdc]
      exact Algebra.commutes _ _
    · have hwτ : τ (d - τ d) = -(d - τ d) := by rw [τ.map_sub, τ.apply_apply, neg_sub]
      have hloc (v : InfinitePlace F) (hv : v.IsReal)
          (hcs : IsSquare (algebraMap F v.Completion c)) :
          ∃ y : Fin n → v.Completion ⊗[F] D, y ≠ 0 ∧
            ∑ j, ∑ k, y j * ((1 : v.Completion) ⊗ₜ[F] H j k) *
              τ.baseChange v.Completion (y k) = 0 := by
        apply (hsplit v hv _).2
        intro has
        obtain ⟨r, hr⟩ := hcs
        have h' := hell v hv has
        rw [hr, _root_.map_mul] at h'
        exact absurd h' (not_lt.mpr (mul_self_nonneg _))
      obtain ⟨x, b, hb, hx⟩ := σ.exists_value_on_pureLine_of_real hdim hsym hI hH hu hw hwτ hc hloc
      refine ⟨x, fun h => ?_, ?_⟩
      · have h' := σ.sesqForm_conjugationSkewGram hdim hsym q x x
        rw [h, zero_mul, hx] at h'
        exact smul_ne_zero hb hw h'
      · rw [hx, mul_smul_comm, smul_mul_assoc, hτd]
        congr 1
        have hT : algebraMap F D t * d = d * algebraMap F D t := Algebra.commutes t d
        simp only [mul_sub, sub_mul, hT]
  refine ⟨x, d, Units.mk0 s hs0, hx0, ?_, ?_⟩
  · -- `σ d = l⁻¹ τ d l` and `σ`-values are skew values times `l`
    have hval : σ.sesqForm P x x = τ.sesqForm H x x * l := by
      rw [σ.sesqForm_conjugationSkewGram hdim hsym q x x, mul_assoc, inv_mul_cancel₀ hl0, mul_one]
    have hσd : σ d = l⁻¹ * τ d * l := by
      change σ d = l⁻¹ * (l * σ d * l⁻¹) * l
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hl0, one_mul, mul_assoc, inv_mul_cancel₀ hl0,
        mul_one]
    rw [hval, hσd, hNrd]
    set W := τ.sesqForm H x x
    calc d * (W * l) * (l⁻¹ * τ d * l) = (d * W) * (l * l⁻¹) * τ d * l := by noncomm_ring
      _ = W * (d * τ d) * l := by rw [mul_inv_cancel₀ hl0, mul_one, hcomm]; noncomm_ring
      _ = ((a : F) * s ^ 2) • (W * l) := by
        rw [hd, ← Algebra.commutes, Algebra.smul_def, mul_assoc]
  · rw [hNrd, Units.val_mk0]

end Langlands.GroupScheme
