import Langlands.BushnellKutzko.TraceDuality
import Langlands.Representation.GodementJacquet.AnalyticData

/-! # Fourier support of a twisted indicator function on matrices

Let `P` be an additive subgroup of the `N × N` matrices over a field `K`, `b'` a matrix and `ψ` a
unitary additive character of `K`. The *twisted indicator*
`Φ(y) = 1_P(y - 1) ψ(-tr(b' (y - 1)))` satisfies `Φ(z + y) = ψ(-tr(b' z)) Φ(y)` for `z ∈ P`.
By translation invariance of the product Haar measure, its plus-sign Fourier integral
`Φ̂(x) = ∫ Φ(y) ψ(⟨y, x⟩) dy`, with the entry pairing `⟨y, x⟩ = tr(y xᵀ)`, satisfies
`Φ̂(x) = ψ(tr(z (xᵀ - b'))) Φ̂(x)` for every `z ∈ P`. Hence `Φ̂(x) ≠ 0` forces
`ψ(tr(z (xᵀ - b'))) = 1` for all `z ∈ P`
(`trace_mul_sub_eq_one_of_rectangularFourierIntegral_ne_zero`). No evaluation of the integral and
no integrability is needed.

For `P = 𝔓^k(𝓛)` (matrices whose linear map lies in the filtration of a lattice chain) the
trace duality `LatticeChain.mem_endFiltration_one_sub_of_forall` turns this into
`c⁻¹ (xᵀ - b') ∈ 𝔓^{1-k}(𝓛)` whenever `ψ(c ·)` is nontrivial on `𝔬_K`
(`LatticeChain.toLin'_mem_endFiltration_of_rectangularFourierIntegral_ne_zero`).

This belongs to the analytic part of the proof of T2 (see `ConductorFormula`): it bounds the
support of the Fourier transform of the test function attached to a stratum contained in a
representation.
-/

noncomputable section

open MeasureTheory Langlands.HarmonicAnalysis ValuativeRel

namespace Langlands.BushnellKutzko

universe u

section Translation

variable {K : Type u} [Field K] [TopologicalSpace K] [MeasurableSpace K] [MeasurableAdd K]
  {r s : ℕ}

omit [TopologicalSpace K] [MeasurableSpace K] [MeasurableAdd K] in
/-- The entry pairing is additive in its first argument. -/
theorem rectangularPairing_add_left (a a' b : Matrix (Fin r) (Fin s) K) :
    rectangularPairing (a + a') b = rectangularPairing a b + rectangularPairing a' b := by
  simp only [rectangularPairing, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

/-- If `Φ(z + y) = c Φ(y)` for all `y`, then the Fourier integral of `Φ` at `x` vanishes unless
`c ψ(⟨z, x⟩) = 1`. Only translation invariance of the product Haar measure is used. -/
theorem rectangularFourierIntegral_eq_zero_of_add_left (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure]
    {Φ : Matrix (Fin r) (Fin s) K → ℂ} {z : Matrix (Fin r) (Fin s) K} {c : ℂ}
    (hΦ : ∀ y, Φ (z + y) = c * Φ y) (x : Matrix (Fin r) (Fin s) K)
    (hc : c * ψ.complex (rectangularPairing z x) ≠ 1) :
    rectangularFourierIntegral ψ ν Φ x = 0 := by
  have hinv : (RankinSelberg.rectangularMeasure ν r s).IsAddLeftInvariant :=
    inferInstanceAs
      (Measure.pi (fun _ : Fin r => Measure.pi (fun _ : Fin s => ν.measure))).IsAddLeftInvariant
  have hadd : MeasurableAdd (Matrix (Fin r) (Fin s) K) :=
    inferInstanceAs (MeasurableAdd (Fin r → Fin s → K))
  have key : rectangularFourierIntegral ψ ν Φ x =
      (c * ψ.complex (rectangularPairing z x)) * rectangularFourierIntegral ψ ν Φ x := by
    calc rectangularFourierIntegral ψ ν Φ x
        = MeasureTheory.integral (RankinSelberg.rectangularMeasure ν r s)
            (fun y => Φ (z + y) * ψ.complex (rectangularPairing (z + y) x)) :=
          (integral_add_left_eq_self (μ := RankinSelberg.rectangularMeasure ν r s)
            (fun y => Φ y * ψ.complex (rectangularPairing y x)) z).symm
      _ = MeasureTheory.integral (RankinSelberg.rectangularMeasure ν r s)
            (fun y => (c * ψ.complex (rectangularPairing z x)) *
              (Φ y * ψ.complex (rectangularPairing y x))) := by
          congr 1
          funext y
          rw [hΦ, rectangularPairing_add_left, AddChar.map_add_eq_mul]
          ring
      _ = _ := integral_const_mul _ _
  have h1 : (1 - c * ψ.complex (rectangularPairing z x)) *
      rectangularFourierIntegral ψ ν Φ x = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (Ne.symm hc))

end Translation

section TwistedIndicator

variable {K : Type u} [Field K] [TopologicalSpace K] {N : ℕ}

/-- The twisted indicator `Φ(y) = 1_P(y - 1) ψ(-tr(b' (y - 1)))` of an additive subgroup `P` of
the `N × N` matrices, a matrix `b'` and an additive character `ψ`. -/
def twistedIndicator (ψ : UnitaryAdditiveCharacter K) (P : AddSubgroup (Matrix (Fin N) (Fin N) K))
    (b' : Matrix (Fin N) (Fin N) K) : Matrix (Fin N) (Fin N) K → ℂ :=
  Set.indicator {y | y - 1 ∈ P} fun y => ψ.complex (-(b' * (y - 1)).trace)

theorem twistedIndicator_apply_of_mem (ψ : UnitaryAdditiveCharacter K)
    (P : AddSubgroup (Matrix (Fin N) (Fin N) K)) (b' : Matrix (Fin N) (Fin N) K)
    {y : Matrix (Fin N) (Fin N) K} (hy : y - 1 ∈ P) :
    twistedIndicator ψ P b' y = ψ.complex (-(b' * (y - 1)).trace) :=
  Set.indicator_of_mem (s := {y | y - 1 ∈ P}) hy _

theorem twistedIndicator_apply_of_not_mem (ψ : UnitaryAdditiveCharacter K)
    (P : AddSubgroup (Matrix (Fin N) (Fin N) K)) (b' : Matrix (Fin N) (Fin N) K)
    {y : Matrix (Fin N) (Fin N) K} (hy : y - 1 ∉ P) :
    twistedIndicator ψ P b' y = 0 :=
  Set.indicator_of_notMem (s := {y | y - 1 ∈ P}) hy _

/-- Translating the twisted indicator by an element `z ∈ P` multiplies it by `ψ(-tr(b' z))`. -/
theorem twistedIndicator_add_left (ψ : UnitaryAdditiveCharacter K)
    (P : AddSubgroup (Matrix (Fin N) (Fin N) K)) (b' : Matrix (Fin N) (Fin N) K)
    {z : Matrix (Fin N) (Fin N) K} (hz : z ∈ P) (y : Matrix (Fin N) (Fin N) K) :
    twistedIndicator ψ P b' (z + y) = ψ.complex (-(b' * z).trace) * twistedIndicator ψ P b' y := by
  have hsub : z + y - 1 = z + (y - 1) := by abel
  by_cases hy : y - 1 ∈ P
  · rw [twistedIndicator_apply_of_mem ψ P b' (hsub ▸ P.add_mem hz hy),
      twistedIndicator_apply_of_mem ψ P b' hy, hsub, Matrix.mul_add, Matrix.trace_add, neg_add,
      AddChar.map_add_eq_mul]
  · have hzy : z + y - 1 ∉ P := by
      rw [hsub]
      exact fun h => hy ((P.add_mem_cancel_left hz).1 h)
    rw [twistedIndicator_apply_of_not_mem ψ P b' hzy, twistedIndicator_apply_of_not_mem ψ P b' hy,
      mul_zero]

omit [TopologicalSpace K] in
/-- The entry pairing of square matrices is `⟨z, x⟩ = tr(z xᵀ)`. -/
theorem rectangularPairing_eq_trace (z x : Matrix (Fin N) (Fin N) K) :
    rectangularPairing z x = (z * x.transpose).trace := by
  simp [rectangularPairing, Matrix.trace, Matrix.mul_apply]

variable [MeasurableSpace K] [MeasurableAdd K]

/-- **Fourier support of the twisted indicator.** If the Fourier integral of the twisted
indicator of `(P, b')` is nonzero at `x`, then `ψ(tr(z (xᵀ - b'))) = 1` for every `z ∈ P`. -/
theorem trace_mul_sub_eq_one_of_rectangularFourierIntegral_ne_zero
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure]
    (P : AddSubgroup (Matrix (Fin N) (Fin N) K)) (b' x : Matrix (Fin N) (Fin N) K)
    (hx : rectangularFourierIntegral ψ ν (twistedIndicator ψ P b') x ≠ 0) :
    ∀ z ∈ P, ψ.complex (z * (x.transpose - b')).trace = 1 := by
  intro z hz
  by_contra hne
  apply hx
  refine rectangularFourierIntegral_eq_zero_of_add_left ψ ν
    (twistedIndicator_add_left ψ P b' hz) x ?_
  rw [Matrix.mul_sub, Matrix.trace_sub] at hne
  rwa [← AddChar.map_add_eq_mul, rectangularPairing_eq_trace, Matrix.trace_mul_comm b' z,
    neg_add_eq_sub]

end TwistedIndicator

section LatticeChain

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {N : ℕ}

namespace LatticeChain

/-- The additive subgroup of matrices whose linear map lies in `𝔓^k(𝓛)`. -/
def matrixFiltration (𝓛 : LatticeChain 𝒪[K] K (Fin N → K)) (k : ℤ) :
    AddSubgroup (Matrix (Fin N) (Fin N) K) :=
  (𝓛.endFiltration k).toAddSubgroup.comap
    (Matrix.toLin' : Matrix (Fin N) (Fin N) K ≃ₗ[K] _).toLinearMap.toAddMonoidHom

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem mem_matrixFiltration (𝓛 : LatticeChain 𝒪[K] K (Fin N → K)) (k : ℤ)
    (y : Matrix (Fin N) (Fin N) K) :
    y ∈ 𝓛.matrixFiltration k ↔ Matrix.toLin' y ∈ 𝓛.endFiltration k :=
  Iff.rfl

variable [MeasurableSpace K] [MeasurableAdd K]

/-- **Fourier support in terms of the lattice chain**. Let `c ≠ 0` be such that
`ψ(c a) ≠ 1` for some `a ∈ 𝔬_K`. If the Fourier integral of the twisted indicator of
`(𝔓^k(𝓛), b')` is nonzero at `x`, then `c⁻¹ (xᵀ - b') ∈ 𝔓^{1-k}(𝓛)`. -/
theorem toLin'_mem_endFiltration_of_rectangularFourierIntegral_ne_zero
    (𝓛 : LatticeChain 𝒪[K] K (Fin N → K)) (k : ℤ) (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure] {c : K} (hc : c ≠ 0)
    (hψc : ∃ a : 𝒪[K], ψ.complex (c * a) ≠ 1) (b' x : Matrix (Fin N) (Fin N) K)
    (hx : rectangularFourierIntegral ψ ν (twistedIndicator ψ (𝓛.matrixFiltration k) b') x ≠ 0) :
    Matrix.toLin' (c⁻¹ • (x.transpose - b')) ∈ 𝓛.endFiltration (1 - k) := by
  have hsupp := trace_mul_sub_eq_one_of_rectangularFourierIntegral_ne_zero ψ ν
    (𝓛.matrixFiltration k) b' x hx
  let ψc : AddChar K ℂ := ψ.complex.compAddMonoidHom (AddMonoidHom.mulLeft c)
  have hψc_apply : ∀ t, ψc t = ψ.complex (c * t) := fun t => rfl
  refine 𝓛.mem_endFiltration_one_sub_of_forall ψc ?_ ?_
  · obtain ⟨a, ha⟩ := hψc
    exact ⟨a, by rwa [hψc_apply]⟩
  · intro z hz
    have hZ : LinearMap.toMatrix' z ∈ 𝓛.matrixFiltration k := by
      rw [mem_matrixFiltration, Matrix.toLin'_toMatrix']
      exact hz
    have h := hsupp _ hZ
    rw [hψc_apply, ← Matrix.toLin'_toMatrix' z, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
      Matrix.trace_toLin'_eq, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hc, one_mul, Matrix.trace_mul_comm]
    exact h

end LatticeChain

end LatticeChain

end Langlands.BushnellKutzko
