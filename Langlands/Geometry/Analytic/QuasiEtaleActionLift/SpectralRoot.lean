import Langlands.Geometry.Analytic.QuasiEtaleActionLift.SpectralControl
import Langlands.Geometry.Analytic.QuasiEtaleActionLift.SpectralFixedPoint
import Mathlib.Algebra.Polynomial.Taylor

/-! # Uniform perturbation of a simple affinoid root -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open BanachSpectrum Polynomial

variable {K : Type u} {R : Type v} {A : Type w}
  [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedCommRing R] [NormedAlgebra K R] [NormedCommRing A] [NormedAlgebra K A]

/-- Finite tests on the coefficient map ensure a root near the image of the
reference simple root, uniformly after any bounded specialization. -/
theorem exists_spectralRootNear (a : BoundedAlgHom K R A) (P : Polynomial R) (x d : A)
    (hx : P.eval₂ a.toAlgHom.toRingHom x = 0)
    (hd : d * P.derivative.eval₂ a.toAlgHom.toRingHom x = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (D : Finset R) (δ : ℝ), 0 < δ ∧
      ∀ (B : PresentedAffinoidAlgebra K) (l : BoundedAlgHom K A B) (b : BoundedAlgHom K R B),
        (∀ t ∈ D, SpectralBound (b t - l (a t)) δ) →
        ∃ y : B, P.eval₂ b.toAlgHom.toRingHom y = 0 ∧ SpectralBound (y - l x) ε := by
  let N := max 1 P.natDegree
  let I := Finset.range (N + 1)
  let V (i : ℕ) := (X : Polynomial A).coeff i - d * (hasseDeriv i P).eval₂ a.toAlgHom.toRingHom x
  let Q (B : PresentedAffinoidAlgebra K) (l : BoundedAlgHom K A B) (b : BoundedAlgHom K R B) :=
    X - Polynomial.C (l d) * (P.map b.toAlgHom.toRingHom).taylor (l x)
  let F (i : ℕ) (B : PresentedAffinoidAlgebra K) (l : BoundedAlgHom K A B)
      (b : BoundedAlgHom K R B) (_ : Unit → B) := (Q B l b).coeff i
  have hF i : HasSpectralControlAt a (fun _ : Unit => x) (V i) (F i) := by
    have hEq : F i = fun B l b _ => l ((X : Polynomial A).coeff i) -
        l d * (hasseDeriv i P).eval₂ b.toAlgHom.toRingHom (l x) := by
      funext B l b y
      have hX : l ((X : Polynomial A).coeff i) = (X : Polynomial B).coeff i := by
        rw [Polynomial.coeff_X, Polynomial.coeff_X]
        split_ifs <;> change l.toAlgHom _ = _ <;> simp only [map_one, map_zero]
      simp only [F, Q, coeff_sub, coeff_C_mul, taylor_coeff, hasseDeriv_map, eval_map, hX]
    rw [hEq]
    exact (HasSpectralControlAt.const ((X : Polynomial A).coeff i)).sub
      ((HasSpectralControlAt.const d).mul
        (HasSpectralControlAt.eval₂ (hasseDeriv i P) (HasSpectralControlAt.const x)))
  have hV0 : V 0 = 0 := by
    simp only [V, coeff_X_zero, hasseDeriv_zero, LinearMap.id_apply, hx, mul_zero, sub_zero]
  have hV1 : V 1 = 0 := by
    simp only [V, coeff_X_one, hasseDeriv_one, hd, sub_self]
  let M := 1 + ∑ i ∈ I, ‖V i‖
  have hM : 1 ≤ M := by
    dsimp [M]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hVM {i : ℕ} (hi : i ∈ I) : ‖V i‖ ≤ M :=
    (Finset.single_le_sum (fun j _ => norm_nonneg (V j)) hi).trans
      (le_add_of_nonneg_left zero_le_one)
  let r := min ε ((1 / 2) / M)
  have hr : 0 < r := lt_min hε (div_pos (by norm_num) hM0)
  have hrM : M * r ≤ 1 / 2 := by
    rw [mul_comm, ← le_div_iff₀ hM0]
    exact min_le_right _ _
  have hr1 : r ≤ 1 := by
    apply (min_le_right _ _).trans
    rw [div_le_iff₀ hM0, one_mul]
    exact (by norm_num : (1 / 2 : ℝ) ≤ 1).trans hM
  let tol (i : ℕ) := if i = 0 then r else if i = 1 then (1 / 2 : ℝ) else 1
  have htol i : 0 < tol i := by
    dsimp [tol]
    split_ifs <;> first | exact hr | norm_num
  obtain ⟨D, δ, hδ, hclose⟩ := HasSpectralControlAt.finite (a := a) (x := fun _ : Unit => x)
    I tol V F (fun i _ => htol i) (fun i _ => hF i)
  refine ⟨D, δ, hδ, fun B l b hb => ?_⟩
  let q := Q B l b
  have hqdeg : q.natDegree ≤ N := by
    dsimp only [q, Q]
    apply (natDegree_sub_le _ _).trans
    exact max_le (natDegree_X_le.trans (le_max_left _ _)) ((natDegree_C_mul_le _ _).trans
      ((natDegree_taylor _ _).le.trans (natDegree_map_le.trans (le_max_right _ _))))
  have hcoeff (i : ℕ) (hi : i ≤ N) : SpectralBound (q.coeff i - l (V i)) (tol i) :=
    hclose B l b (fun _ => l x) hb (fun _ => by simpa using spectralBound_zero hδ.le)
      i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have hc : SpectralBound (q.coeff 0) r := by
    have hz : l (V 0) = 0 := hV0 ▸ l.toAlgHom.map_zero
    simpa only [hz, sub_zero, tol, ite_eq_left rfl] using hcoeff 0 (Nat.zero_le _)
  have hb' (i : Fin N) (p : BanachSpectrum B) : p (q.coeff (i.val + 1)) * r ^ i.val ≤ 1 / 2 := by
    have hi : i.val + 1 ≤ N := Nat.succ_le_of_lt i.isLt
    have h := hcoeff (i.val + 1) hi p
    by_cases hi0 : i.val = 0
    · have hz : l (V 1) = 0 := hV1 ▸ l.toAlgHom.map_zero
      simpa [hi0, tol, hz] using h
    · have hpv : p (l (V (i.val + 1))) ≤ M :=
        ((BanachSpectrum.comap l.toBoundedRingHom p).le_norm _).trans
          (hVM (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
      have hdif₁ : p (q.coeff (i.val + 1) - l (V (i.val + 1))) ≤ 1 := by
        simpa [tol, hi0] using h
      have hdif := hdif₁.trans hM
      have hsum := p.isNonarchimedean (K := K) (q.coeff (i.val + 1) - l (V (i.val + 1)))
        (l (V (i.val + 1)))
      rw [sub_add_cancel] at hsum
      have hbound := hsum.trans (max_le hdif hpv)
      have hpow : r ^ i.val ≤ r := by
        simpa only [pow_one] using pow_le_pow_of_le_one hr.le hr1 (Nat.one_le_iff_ne_zero.mpr hi0)
      exact (mul_le_mul hbound hpow (pow_nonneg hr.le _) hM0.le).trans hrM
  obtain ⟨z, hz, hzr⟩ := exists_spectralPolynomialFixedPoint B (fun i : Fin N => i.val)
    (q.coeff 0) (fun i => q.coeff (i.val + 1)) hr (by norm_num) (by norm_num) hc hb'
  have hz' : z = q.eval z := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hqdeg), Finset.sum_range_succ',
      ← Fin.sum_univ_eq_sum_range]
    simpa only [pow_zero, mul_one, add_comm _ (q.coeff 0)] using hz
  refine ⟨z + l x, ?_, ?_⟩
  · have heval : z = z - l d * P.eval₂ b.toAlgHom.toRingHom (z + l x) := by
      simpa only [q, Q, eval_sub, eval_X, eval_mul, eval_C, taylor_eval, eval_map] using hz'
    have hzero : l d * P.eval₂ b.toAlgHom.toRingHom (z + l x) = 0 := by
      exact sub_eq_self.mp heval.symm
    have hinv : l (P.derivative.eval₂ a.toAlgHom.toRingHom x) * l d = 1 := by
      rw [mul_comm]
      change l.toAlgHom d * l.toAlgHom (P.derivative.eval₂ a.toAlgHom.toRingHom x) = 1
      rw [← map_mul, hd, map_one]
    calc
      P.eval₂ b.toAlgHom.toRingHom (z + l x) =
          l (P.derivative.eval₂ a.toAlgHom.toRingHom x) *
            (l d * P.eval₂ b.toAlgHom.toRingHom (z + l x)) := by
        rw [← mul_assoc, hinv, one_mul]
      _ = 0 := by rw [hzero, mul_zero]
  · rw [add_sub_cancel_right]
    exact (show SpectralBound z r from hzr).mono (min_le_left _ _)

end Langlands.Analytic.PresentedAffinoidAlgebra
