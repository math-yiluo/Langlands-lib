import Langlands.Representation.RankinSelberg.GroupedLFactorReduction

/-! # Actual shifted analytic L-products for supplied segment heads -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance analyticSegmentTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- A polynomial's spectral reciprocal is the finite product of the supplied
polynomial reciprocals translated by the supplied real shifts. -/
def IsPadicShiftedReciprocalProduct {I : Type*} [Fintype I]
    (P : ℂ[X]) (base : I → ℂ[X]) (shift : I → ℝ) : Prop :=
  ∀ z : ℂ,
    (P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality z))⁻¹ =
      ∏ i : I,
        ((base i).eval (spectralPoint F.canonicalTopologicalData.residueCardinality
          (z + (shift i : ℂ))))⁻¹

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

/-- Polynomial substitution for a real determinant twist evaluates at the
translated complex spectral parameter, including at denominator zeros. -/
theorem realTwistPolynomial_eval_spectral (s : ℝ) (P : ℂ[X]) (z : ℂ) :
    (realTwistPolynomial F s P).eval
        (spectralPoint F.canonicalTopologicalData.residueCardinality z) =
      P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality (z + (s : ℂ))) := by
  change (P.comp (C _ * X)).eval _ = _
  rw [eval_comp, eval_mul, eval_C, eval_X]
  congr 1
  exact (spectralPoint_add F.canonicalTopologicalData.residueCardinality_gt_one z (s : ℂ)).symm

/-- Every certificate for the two actually twisted actions has the translated
reciprocal of the original pair's certificate. -/
theorem IsPadicRankLPolynomial.reciprocal_eq_of_realTwists
    {n t : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (GeneralLinear t F.Carrier) W}
    {R P : ℂ[X]} (hR : IsPadicRankLPolynomial F ψ ν.val π σ R)
    (s t' : ℝ)
    (hP : IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) s π)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm t) t' σ) P)
    (z : ℂ) :
    (P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality z))⁻¹ =
      (R.eval (spectralPoint F.canonicalTopologicalData.residueCardinality
        (z + ((s + t' : ℝ) : ℂ))))⁻¹ := by
  rw [hP.unique (hR.twist_real F ψ ν s t'), realTwistPolynomial_eval_spectral,
    realTwistPolynomial_eval_spectral]
  congr 3
  push_cast
  ring

/-- The polynomial product for segment heads gives the actual finite product
of translated spectral reciprocals after arbitrary real twists of both supplied
heads. The segment-head formula and the base-pair certificate remain explicit. -/
theorem reciprocal_of_segmentHeads_realTwists
    (hH : SegmentHeadLFactorStatement.{uF, uV, uW})
    (Δ : F.canonicalTopologicalData.Segment.{uV, uF})
    (Δ' : F.canonicalTopologicalData.Segment.{uW, uF})
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (σ : SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear Δ'.degree F.Carrier))
    (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (A' : SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := Δ'.rank))
    (hπ : F.canonicalTopologicalData.IsSegmentHead Δ π)
    (hσ : F.canonicalTopologicalData.IsSegmentHead Δ' σ)
    (hA : Δ.base.IsRepresentedBy A) (hA' : Δ'.base.IsRepresentedBy A')
    {R P : ℂ[X]}
    (hR : IsPadicRankLPolynomial F ψ ν.val A.obj.representation A'.obj.representation R)
    (s t : ℝ)
    (hP : IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm Δ.degree) s π.representation)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm Δ'.degree) t σ.representation) P) :
    IsPadicShiftedReciprocalProduct F P
      (fun _ : Fin (min Δ.length Δ'.length) => R)
      (fun j => (Δ.length : ℝ) + Δ'.length - 2 - (j : ℕ) + s + t) := by
  intro z
  obtain ⟨P₀, Q, hP₀, hQ, hprod⟩ := hH p F ψ ν Δ Δ' π σ A A' hπ hσ hA hA'
  rw [hP₀.reciprocal_eq_of_realTwists F ψ ν s t hP z, hprod, eval_prod,
    ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hQj := hQ j
  have hQj' : IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm Δ.rank)
        ((Δ.length : ℝ) + Δ'.length - 2 - (j : ℕ)) A.obj.representation)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm Δ'.rank) 0
        A'.obj.representation) (Q j) := by
    simpa only [realPowerTwist_zero] using hQj
  rw [hR.reciprocal_eq_of_realTwists F ψ ν _ 0 hQj' _]
  congr 3
  push_cast
  ring

end Langlands.RankinSelberg
