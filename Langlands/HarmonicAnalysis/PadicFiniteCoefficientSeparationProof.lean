import Langlands.HarmonicAnalysis.PadicFiniteCoefficientSeparationStatement
import Langlands.HarmonicAnalysis.PadicAdditiveCharacterSelfDuality

/-! Common prime-power scaling separates a finite family of coefficients. -/

noncomputable section

namespace Langlands.HarmonicAnalysis

universe u

/-- Simultaneous detection on a prescribed lattice after common prime scaling. -/
theorem padicFiniteCoefficientSeparation :
    PadicFiniteCoefficientSeparationStatement.{u} := by
  intro p _ F T
  let := T.topology
  intro ψ s m
  classical
  let B : ℕ := s.sup (fun a => (T.ord a + T.additiveConductor ψ - m + 1).toNat)
  refine ⟨B, fun N hN a ha => ?_⟩
  constructor
  · intro h
    by_contra hne
    have hp : (p : F.Carrier) ≠ 0 := by
      simpa only [map_natCast] using
        ((map_ne_zero (algebraMap (Padic p) F.Carrier)).mpr
          (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : Padic p) ≠ 0))
    have hc : (p : F.Carrier) ^ (-(N : ℤ)) ≠ 0 := zpow_ne_zero _ hp
    have hd : (p : F.Carrier) ^ (-(N : ℤ)) * a ≠ 0 := mul_ne_zero hc hne
    have hmem := T.mem_additiveLattice_of_forall_complex_mul_eq_one ψ m _ h
    have hval :
        T.discreteValuation ((p : F.Carrier) ^ (-(N : ℤ)) * a) =
          WithZero.exp (-T.ord ((p : F.Carrier) ^ (-(N : ℤ)) * a)) := by
      simp only [PadicField.TopologicalData.ord, neg_neg]
      exact (WithZero.exp_log (T.discreteValuation.ne_zero_iff.mpr hd)).symm
    rw [T.mem_additiveLattice, hval] at hmem
    have hle := WithZero.exp_le_exp.mp hmem
    rw [T.ord_mul hc hne, T.ord_zpow] at hle
    have hB : (T.ord a + T.additiveConductor ψ - m + 1).toNat ≤ B :=
      Finset.le_sup (f := fun b => (T.ord b + T.additiveConductor ψ - m + 1).toNat) ha
    have hbound : T.ord a + T.additiveConductor ψ - m + 1 ≤ (N : ℤ) := by
      have hcast : ((T.ord a + T.additiveConductor ψ - m + 1).toNat : ℤ) ≤ N := by
        exact_mod_cast hB.trans hN
      exact (Int.self_le_toNat _).trans hcast
    have he : 1 ≤ T.ord (p : F.Carrier) := T.ord_prime_pos
    have hprod : (N : ℤ) ≤ (N : ℤ) * T.ord (p : F.Carrier) := by
      nlinarith [Int.natCast_nonneg N]
    nlinarith
  · rintro rfl x hx
    simp

end Langlands.HarmonicAnalysis
