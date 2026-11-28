import Langlands.HarmonicAnalysis.UnitConjugation.InvariantDistribution
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.NoncommRing

/-! # Clopen conjugacy orbits in the root locus of a separable polynomial -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Filter Polynomial Set
open scoped _root_.Topology

universe u v

section Algebra

variable {F : Type u} [CommRing F] {A : Type v} [Ring A] [Algebra F A]

private def powerDividedDifference (x y : A) : ℕ → A
  | 0 => 0
  | n + 1 => x * powerDividedDifference x y n + y ^ n

private theorem mul_powerDividedDifference_sub (x y : A) (n : ℕ) :
    x * powerDividedDifference x y n - powerDividedDifference x y n * y = x ^ n - y ^ n := by
  induction n with
  | zero => simp [powerDividedDifference]
  | succ n ih =>
    calc
      _ = x * (x * powerDividedDifference x y n - powerDividedDifference x y n * y) +
          x * y ^ n - y ^ (n + 1) := by
        rw [powerDividedDifference, pow_succ y]
        noncomm_ring
      _ = _ := by rw [ih, mul_sub, sub_add_cancel, ← pow_succ']

private theorem powerDividedDifference_self (x : A) (n : ℕ) :
    powerDividedDifference x x n = n • x ^ (n - 1) := by
  rcases n with _ | n
  · simp [powerDividedDifference]
  simp only [add_tsub_cancel_right]
  induction n with
  | zero => simp [powerDividedDifference]
  | succ n ih =>
    rw [powerDividedDifference, ih, mul_smul_comm, ← pow_succ']
    exact (succ_nsmul (x ^ (n + 1)) (n + 1)).symm

private def dividedDifference (p : F[X]) (x y : A) : A :=
  p.sum fun n c => c • powerDividedDifference x y n

private theorem mul_dividedDifference_sub (p : F[X]) (x y : A) :
    x * dividedDifference p x y - dividedDifference p x y * y = aeval x p - aeval y p := by
  simp only [dividedDifference, aeval_def, eval₂_eq_sum, Polynomial.sum_def, Algebra.smul_def,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← mul_assoc x, ← Algebra.commutes (p.coeff n) x, mul_assoc, mul_assoc,
    ← mul_sub, mul_powerDividedDifference_sub, mul_sub]

private theorem dividedDifference_self (p : F[X]) (x : A) :
    dividedDifference p x x = aeval x p.derivative := by
  rw [derivative_apply]
  simp only [dividedDifference, Polynomial.sum_def, map_sum, map_mul, aeval_C, map_pow,
    aeval_X, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro n _
  rw [powerDividedDifference_self, nsmul_eq_mul, mul_assoc]
  simp only [map_natCast]

/-- The derivative of a separable polynomial evaluates to a unit at any algebra-valued root. -/
theorem isUnit_aeval_derivative_of_separable {p : F[X]} (hp : p.Separable) {y : A}
    (hy : aeval y p = 0) : IsUnit (aeval y p.derivative) := by
  obtain ⟨a, b, hab⟩ := (separable_def' p).mp hp
  have h : aeval y b * aeval y p.derivative = 1 := by
    simpa only [map_add, map_mul, map_one, hy, mul_zero, zero_add] using congrArg (aeval y) hab
  refine isUnit_iff_exists.mpr ⟨aeval y b, ?_, h⟩
  rw [← ((Commute.all b p.derivative).map (aeval y)).eq, h]

end Algebra

section Topology

variable {F : Type u} [CommRing F] {A : Type v} [Ring A] [Algebra F A]
  [TopologicalSpace A] [IsTopologicalRing A] [ContinuousConstSMul F A]

private theorem continuous_powerDividedDifference (y : A) (n : ℕ) :
    Continuous (fun x : A => powerDividedDifference x y n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact (continuous_id.mul ih).add continuous_const

/-- A sufficiently close root of the same separable polynomial is conjugate to `y`. -/
theorem eventually_conjugate_of_aeval_eq_zero (hUnits : IsOpen {a : A | IsUnit a})
    {p : F[X]} (hp : p.Separable) {y : A} (hy : aeval y p = 0) :
    ∀ᶠ x in 𝓝 y, aeval x p = 0 → ∃ u : Aˣ, conjugationHomeomorph u y = x := by
  have hc : Continuous (fun x : A => dividedDifference p x y) := by
    simp only [dividedDifference, Polynomial.sum_def]
    exact continuous_finsetSum _ fun n _ =>
      (continuous_powerDividedDifference y n).const_smul _
  have hu : {x | IsUnit (dividedDifference p x y)} ∈ 𝓝 y :=
    (hUnits.preimage hc).mem_nhds (by
      change IsUnit (dividedDifference p y y)
      rw [dividedDifference_self]
      exact isUnit_aeval_derivative_of_separable hp hy)
  filter_upwards [hu] with x hx hroot
  obtain ⟨u, hu⟩ := (show IsUnit (dividedDifference p x y) from hx)
  refine ⟨u, ?_⟩
  symm
  rw [conjugationHomeomorph_apply, u.eq_mul_inv_iff_mul_eq, hu]
  exact sub_eq_zero.mp (by rw [mul_dividedDifference_sub, hroot, hy, sub_self])

end Topology

/-- In an algebra with open unit locus, each conjugacy orbit in the root locus of a separable
polynomial is relatively clopen. -/
def SeparableRootOrbitClopenStatement : Prop :=
  ∀ (F : Type u) [CommRing F] (A : Type v) [Ring A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [ContinuousConstSMul F A],
    IsOpen {a : A | IsUnit a} → ∀ (p : F[X]), p.Separable →
    ∀ s : A, aeval s p = 0 →
      IsClopen ((Subtype.val : {x : A | aeval x p = 0} → A) ⁻¹'
        conjugationSaturation ({s} : Set A))

theorem separableRootOrbitClopen : SeparableRootOrbitClopenStatement.{u, v} := by
  intro F _ A _ _ _ _ _ hUnits p hp s hs
  let R := {x : A | aeval x p = 0}
  let O := conjugationSaturation ({s} : Set A)
  have hmove (u : Aˣ) {x : A} (hx : x ∈ O) : conjugationHomeomorph u x ∈ O := by
    obtain ⟨v, z, hz, hv⟩ := mem_conjugationSaturation_iff.mp hx
    exact mem_conjugationSaturation_iff.mpr ⟨u * v, z, hz, by
      change conjugationHomeomorph (u * v) z = conjugationHomeomorph u x
      rw [conjugationHomeomorph_mul, show conjugationHomeomorph v z = x from hv]⟩
  have hlocal (y : R) : ∀ᶠ x : R in 𝓝 y, (x : A) ∈ O ↔ (y : A) ∈ O := by
    have h := continuous_subtype_val.continuousAt.eventually
      (eventually_conjugate_of_aeval_eq_zero hUnits hp y.property)
    filter_upwards [h] with x hx
    obtain ⟨u, hu⟩ := hx x.property
    refine ⟨fun hxO => ?_, fun hy => hu ▸ hmove u hy⟩
    have h' := hmove u⁻¹ hxO
    rwa [← hu, ← conjugationHomeomorph_symm, Homeomorph.symm_apply_apply] at h'
  refine ⟨?_, ?_⟩
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    filter_upwards [hlocal y] with x hx
    exact fun hxO => hy (hx.mp hxO)
  · rw [isOpen_iff_mem_nhds]
    intro y hy
    filter_upwards [hlocal y] with x hx
    exact hx.mpr hy

end Langlands.HarmonicAnalysis.UnitConjugation
