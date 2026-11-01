import Langlands.Representation.GodementJacquet.SupercuspidalLaurentComparison
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Nonzero monomial comparison of Fourier-regular matrix operators -/

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial

/-- Every nonzero complex value is attained by the spectral parameter. -/
theorem exists_spectralUnit_eq {q : ℕ} (hq : 1 < q) (x : ℂˣ) :
    ∃ s : ℂ, spectralUnit (Nat.zero_lt_one.trans hq) s = x := by
  have hlog : (Real.log (q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (show (1 : ℝ) < q by exact_mod_cast hq)).ne'
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_one.trans hq).ne'
  refine ⟨-Complex.log (x : ℂ) / (Real.log (q : ℝ) : ℂ), Units.ext ?_⟩
  rw [coe_spectralUnit, spectralPoint, Complex.cpow_def_of_ne_zero hq0,
    ← Complex.natCast_log]
  have he : (Real.log (q : ℝ) : ℂ) *
      -(-Complex.log (x : ℂ) / (Real.log (q : ℝ) : ℂ)) = Complex.log (x : ℂ) := by
    field_simp
  rw [he, Complex.exp_log x.ne_zero]

/-- A complex Laurent polynomial without a nonzero root is a nonzero monomial. -/
theorem exists_monomial_of_laurentEval_ne_zero (A : LaurentCoefficients)
    (hA : ∀ x : ℂˣ, laurentEval x A ≠ 0) :
    ∃ (c : ℂˣ) (k : ℤ), A = LaurentPolynomial.C (c : ℂ) * LaurentPolynomial.T k := by
  obtain ⟨n, P, hP⟩ := LaurentPolynomial.exists_T_pow A
  have hP0 : P ≠ 0 := by
    intro hz
    have he := congrArg (laurentEval (1 : ℂˣ)) hP
    simp only [hz, map_zero, map_mul, laurentEval_T, Units.val_one, one_zpow, mul_one] at he
    exact hA 1 he.symm
  have hr : ∀ z ∈ P.roots, z = 0 := by
    intro z hz
    by_contra hz0
    have he := congrArg (laurentEval (Units.mk0 z hz0)) hP
    simp only [laurentEval_toLaurent, map_mul, laurentEval_T, Units.val_mk0] at he
    rw [(Polynomial.mem_roots hP0).mp hz] at he
    exact (mul_ne_zero (hA _) (zpow_ne_zero _ hz0)) he.symm
  have hprod : (P.roots.map (fun z => (X : ℂ[X]) - C z)).prod = X ^ P.roots.card := by
    have hm : P.roots.map (fun z => (X : ℂ[X]) - C z) =
        P.roots.map (fun _ => (X : ℂ[X])) := by
      apply Multiset.map_congr rfl
      intro z hz
      rw [hr z hz, C_0, sub_zero]
    rw [hm, Multiset.map_const', Multiset.prod_replicate]
  have hrepr : P = C P.leadingCoeff * X ^ P.roots.card := by
    exact ((IsAlgClosed.splits P).eq_prod_roots).trans
      (congrArg (fun Q => C P.leadingCoeff * Q) hprod)
  refine ⟨Units.mk0 P.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hP0),
    (P.roots.card : ℤ) - n, ?_⟩
  have ha : A = Polynomial.toLaurent P * LaurentPolynomial.T (-(n : ℤ)) := by
    rw [hP, mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel,
      LaurentPolynomial.T_zero, mul_one]
  change A = LaurentPolynomial.C P.leadingCoeff *
    LaurentPolynomial.T ((P.roots.card : ℤ) - n)
  calc A = Polynomial.toLaurent P * LaurentPolynomial.T (-(n : ℤ)) := ha
    _ = Polynomial.toLaurent (C P.leadingCoeff * X ^ P.roots.card) *
        LaurentPolynomial.T (-(n : ℤ)) := congrArg
          (fun Q => Polynomial.toLaurent Q * LaurentPolynomial.T (-(n : ℤ))) hrepr
    _ = _ := by rw [map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow,
      mul_assoc, ← LaurentPolynomial.T_add, sub_eq_add_neg]

end Langlands.RankinSelberg

namespace Langlands.GodementJacquet

open HarmonicAnalysis

universe uF uV

section Fourier

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K]
  [TotallyDisconnectedSpace K] [T2Space K]

/-- The actual plus Fourier transform restricted to the two-support-condition
subspace, with inverse the actual inverse Fourier transform. -/
def fourierRegularMatrixFourierEquiv (d : ℕ)
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
    (hsd : IsSelfDual ψ ν) :
    fourierRegularMatrixTests d ψ ν hsd ≃ₗ[ℂ] fourierRegularMatrixTests d ψ ν hsd where
  toFun Φ := ⟨rectangularFourierEquiv ψ ν d d hsd Φ.val,
    fourier_mem_fourierRegularMatrixTests d ψ ν hsd Φ.property⟩
  invFun Φ := ⟨(rectangularFourierEquiv ψ ν d d hsd).symm Φ.val,
    inverseFourier_mem_fourierRegularMatrixTests d ψ ν hsd Φ.property⟩
  left_inv Φ := Subtype.ext ((rectangularFourierEquiv ψ ν d d hsd).symm_apply_apply Φ.val)
  right_inv Φ := Subtype.ext ((rectangularFourierEquiv ψ ν d d hsd).apply_symm_apply Φ.val)
  map_add' Φ Ψ := Subtype.ext ((rectangularFourierEquiv ψ ν d d hsd).map_add Φ.val Ψ.val)
  map_smul' c Φ := Subtype.ext ((rectangularFourierEquiv ψ ν d d hsd).map_smul c Φ.val)

end Fourier

namespace Padic

open MeasureTheory RankinSelberg

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance monomialComparisonTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance monomialComparisonValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance monomialComparisonLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance monomialComparisonT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance monomialComparisonDisconnected : TotallyDisconnectedSpace F.Carrier :=
  (padicLatticeGeometry F F.canonicalTopologicalData).1
local instance monomialComparisonMeasurable : MeasurableSpace F.Carrier := borel _
local instance monomialComparisonBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance monomialComparisonGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance monomialComparisonGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A scalar comparison with a supercuspidal Fourier-side family cannot vanish. -/
theorem scalar_ne_zero_of_fourierRegular_comparison [Nontrivial V]
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V) (hρ : IsSmooth ρ)
    (σ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hσ : GeneralLinear.IsSupercuspidal σ)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (s t c : ℂ)
    (hc : ∀ Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd,
      regularMatrixZetaOperator F σ hσ.1.1 (t - s)
          ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val, Φ.property.2⟩ =
        c • fourierRegularMatrixZetaOperator F ρ hρ ψ ν hsd s Φ) : c ≠ 0 := by
  intro hzero
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨Ψ, u, hu, hΨ⟩ := exists_fourierRegular_constant_output F hm σ hσ ψ ν hsd v hv
  obtain ⟨Φ, hΦ⟩ := (fourierRegularMatrixFourierEquiv (m + 1) ψ ν hsd).surjective Ψ
  have htest : (⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val,
      Φ.property.2⟩ : regularMatrixTests (K := F.Carrier) (m + 1)) =
      ⟨Ψ.val, Ψ.property.1⟩ := by
    apply Subtype.ext
    exact congrArg (fun Θ : fourierRegularMatrixTests (m + 1) ψ ν hsd => Θ.val) hΦ
  have he := congrArg (fun L : Module.End ℂ V => L v) (hc Φ)
  rw [htest, hΨ (t - s), hzero, zero_smul, LinearMap.zero_apply] at he
  exact hu he

/-- Supercuspidality on both actual operator sides makes the Laurent comparison
scalar a single nonzero monomial. The analytic cross identity remains explicit. -/
theorem exists_monomial_scalar_of_fourierRegular_cross
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (σ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hσ : GeneralLinear.IsSupercuspidal σ)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (t : ℂ)
    (hcross : ∀ (s : ℂ) (Φ Ψ : fourierRegularMatrixTests (m + 1) ψ ν hsd),
      fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ *
          regularMatrixZetaOperator F σ hσ.1.1 (t - s)
            ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Ψ.val, Ψ.property.2⟩ =
        regularMatrixZetaOperator F σ hσ.1.1 (t - s)
            ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val, Φ.property.2⟩ *
          fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Ψ) :
    ∃ (c : ℂˣ) (k : ℤ), ∀ (s : ℂ)
      (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd),
      regularMatrixZetaOperator F σ hσ.1.1 (t - s)
          ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val, Φ.property.2⟩ =
        ((c : ℂ) * spectralPoint F.canonicalTopologicalData.residueCardinality s ^ k) •
          fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ := by
  let := hi
  let : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear (m + 1) F.Carrier)) ρ.asModule
  obtain ⟨A, hA⟩ := exists_laurent_scalar_of_fourierRegular_cross
    F hm ρ hρ hi σ hσ.1.1 ψ ν hsd t hcross
  have hne : ∀ x : ℂˣ, laurentEval x A ≠ 0 := by
    intro x
    obtain ⟨s, rfl⟩ := exists_spectralUnit_eq F.canonicalTopologicalData.residueCardinality_gt_one x
    exact scalar_ne_zero_of_fourierRegular_comparison F hm ρ hρ.1.1 σ hσ ψ ν hsd s t
      _ (hA s)
  obtain ⟨c, k, hck⟩ := exists_monomial_of_laurentEval_ne_zero A hne
  refine ⟨c, k, fun s Φ => ?_⟩
  simpa only [hck, map_mul, laurentEval_C, laurentEval_T, coe_spectralUnit] using hA s Φ

end Padic
end Langlands.GodementJacquet
