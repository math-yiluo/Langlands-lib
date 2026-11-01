import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceGrowth
import Langlands.Representation.Whittaker.SmoothSimpleRootSupportProof

/-! # Integer simple-root support for fixed-slice convergence -/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Langlands.RankinSelberg.TwoBlockLowerFixedSlice

open HarmonicAnalysis Whittaker GeneralLinear TwoBlockConvergence TwoBlockDeformation

universe uF uV

/-- Adjacent diagonal exponents increase by at most `L`. -/
def RootBounded {n : ℕ} (L : ℕ) (lam : Fin (n + 1) → ℤ) : Prop :=
  ∀ i : Fin n, lam i.succ ≤ lam i.castSucc + L

theorem RootBounded.antitone {n L : ℕ} {lam : Fin (n + 1) → ℤ}
    (h : RootBounded L lam) :
    Antitone (fun i : Fin (n + 1) => lam i - (i : ℕ) * (L : ℤ)) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  have := h i
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- Propagating a root bound across any interval costs at most `n * L`. -/
theorem RootBounded.le_of_le {n L : ℕ} {lam : Fin (n + 1) → ℤ}
    (h : RootBounded L lam) {i j : Fin (n + 1)} (hij : i ≤ j) :
    lam j ≤ lam i + (n : ℤ) * L := by
  have hanti := h.antitone hij
  have hi : (0 : ℤ) ≤ (i : ℕ) := by positivity
  have hj : ((j : ℕ) : ℤ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ j.isLt
  have hL : (0 : ℤ) ≤ L := by positivity
  nlinarith

/-- The coordinates in `s` are bounded below, and the remaining ones above. -/
def OppositeCone {n : ℕ} (M : ℕ) (s : Finset (Fin n)) (lam : Fin n → ℤ) : Prop :=
  (∀ i ∈ s, -(M : ℤ) ≤ lam i) ∧ (∀ i ∉ s, lam i ≤ M)

/-- The exponent of decay for the two opposing twists. -/
def twistDegree {n : ℕ} (s : Finset (Fin n)) (lam : Fin n → ℤ) : ℤ :=
  ∑ i, if i ∈ s then lam i else -lam i

/-- The two boundary cutoffs propagate through the corresponding blocks. -/
theorem oppositeCone_of_endpoints {n L M : ℕ} {lam : Fin (n + 1) → ℤ}
    (h : RootBounded L lam) (j : Fin n)
    (hlo : -(M : ℤ) ≤ lam j.castSucc) (hhi : lam j.succ ≤ M) :
    OppositeCone (M + n * L) (Finset.Iic j.castSucc) lam := by
  constructor
  · intro i hi
    have hia : i ≤ j.castSucc := Finset.mem_Iic.mp hi
    have := h.le_of_le hia
    push_cast
    linarith
  · intro i hi
    have hji : j.succ ≤ i := by
      have : ¬ i ≤ j.castSucc := fun hle => hi (Finset.mem_Iic.mpr hle)
      simp only [Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ] at *
      omega
    have := h.le_of_le hji
    push_cast
    linarith

/-- On this cone the twist degree controls every absolute exponent. -/
theorem torusSize_le_twistDegree_add {n M : ℕ} {s : Finset (Fin n)}
    {lam : Fin n → ℤ} (h : OppositeCone M s lam) :
    (torusSize lam : ℤ) ≤ twistDegree s lam + (n : ℤ) * (2 * M) := by
  classical
  have hcoord (i : Fin n) :
      |lam i| ≤ (if i ∈ s then lam i else -lam i) + (2 * M : ℤ) := by
    by_cases hi : i ∈ s
    · rw [ite_eq_left hi]
      have := h.1 i hi
      exact abs_le.mpr ⟨by linarith, by omega⟩
    · rw [ite_eq_right hi]
      have := h.2 i hi
      exact abs_le.mpr ⟨by omega, by linarith⟩
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoord i)
  simpa only [torusSize, Nat.cast_sum, Int.natCast_natAbs, twistDegree,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] using hsum

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField

/-- Canonical torus powers have the normalized residue-cardinality absolute value. -/
theorem normalizedAbs_uniformizer_zpow (z : ℤ) :
    F.canonicalTopologicalData.normalizedAbs
      (((LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) ^ z :
        F.Carrierˣ) : F.Carrier) =
      (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-z) := by
  set T := F.canonicalTopologicalData
  rw [T.normalizedAbs_of_ne_zero (Units.ne_zero _),
    Units.val_zpow_eq_zpow_val, LocalFactor.PadicAbelian.uniformizerUnit_coe,
    T.ord_zpow, T.ord_uniformizer, mul_one]

/-- One integer simple-root bound works for every diagonal and compact factor of
an actual smooth coefficient-image vector. -/
theorem exists_coefficient_rootBounded (ψ : UnitaryAdditiveCharacter F.Carrier)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ n π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ L : ℕ, ∀ (lam : Fin (n + 1) → ℤ) (k : GeneralLinear (n + 1) F.Carrier),
      k ∈ integralOpen F n →
      W.val.val (Iwasawa.torus
        (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * k) ≠ 0 →
      RootBounded L lam := by
  set T := F.canonicalTopologicalData
  obtain ⟨R, _, hR⟩ := smoothSimpleRootSupport F T n ψ V π hπ ell W
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  obtain ⟨L, hL⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop R).exists
  refine ⟨L, fun lam k hk hne i => ?_⟩
  have hk' : k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :=
    (Conductor.mem_integralSubgroup _ n k).2 ((mem_integralOpen F k).1 hk)
  have hs := hR
    (fun j => LocalFactor.PadicAbelian.uniformizerUnit T ^ lam j) k hk' hne i
  rw [div_eq_mul_inv, ← zpow_sub, normalizedAbs_uniformizer_zpow F] at hs
  have hexp : (T.residueCardinality : ℝ) ^ (-(lam i.castSucc - lam i.succ)) ≤
      (T.residueCardinality : ℝ) ^ (L : ℤ) := by
    simpa only [zpow_natCast] using hs.trans hL.le
  have := (zpow_le_zpow_iff_right₀ hq).mp hexp
  omega

end Langlands.RankinSelberg.TwoBlockLowerFixedSlice
