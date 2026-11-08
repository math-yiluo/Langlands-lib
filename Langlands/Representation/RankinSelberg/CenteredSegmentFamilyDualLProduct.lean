import Langlands.Representation.RankinSelberg.CenteredSegmentFamilyLProduct

/-! # The dual Appendix L-product and its gamma expression -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Polynomial Classification

universe uF uV uW uI

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance centeredDualFamilyTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance centeredDualFamilyGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  (ψ' : UnitaryAdditiveCharacter F.Carrier)
  (ν' : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ')

private theorem supercuspidalPairEuler_data_character_independent
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, uV, uW})
    {r m : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) W)
    (hiπ : π.IsIrreducible) (hiσ : σ.IsIrreducible)
    (hsπ : IsSupercuspidal π) (hsσ : IsSupercuspidal σ)
    (huπ : IsUnitarizable π) (huσ : IsUnitarizable σ) :
    (supercuspidalPairEuler hEq ψ' ν' π σ hiπ hiσ hsπ hsσ huπ huσ).data =
      (supercuspidalPairEuler hEq ψ ν π σ hiπ hiσ hsπ hsσ huπ huσ).data := by
  classical
  by_cases h : r = m
  · subst m
    simp [supercuspidalPairEuler]
  · simp [supercuspidalPairEuler, h]

variable {I : Type uI} {n : I → ℕ}
  {δ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n i) F.Carrier)}
  (d : ∀ i, SquareIntegrableSegmentParameter F F.canonicalTopologicalData (n i) (δ i))

/-- The explicit finite Euler data do not depend on the additive character or
self-dual measure; those inputs occur only in their certificates. -/
theorem centeredSegmentBaseEulerFamily_data_character_independent
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    (i j : I) :
    (centeredSegmentBaseEulerFamily hEq ψ' ν' d i j).data =
      (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data := by
  apply supercuspidalPairEuler_data_character_independent F ψ ν ψ' ν' hEq
  exact (d i).positiveBase_isSupercuspidal F F.canonicalTopologicalData

/-- Both the original and actual dual products have the same Appendix function. -/
def IsCenteredSegmentFamilyLProductPair [Fintype I]
    (s : I → ℝ) (P Pdual : ℂ[X]) (base : I → I → ℂ → ℂ) : Prop :=
  IsCenteredSegmentFamilyLProduct F d s P base ∧
    IsCenteredSegmentFamilyLProduct F d s Pdual base

/-- Reversing the order of each mixed pair and transposing the finite product
recovers the same Appendix function, also for another additive character. -/
theorem centeredSegmentFamilyLProduct_of_reverseCertifiedProduct [Fintype I]
    (hH : SegmentHeadLFactorStatement.{uF, max uF uV, max uF uV})
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    (s : I → ℝ) {P : ℂ[X]} (Q : I → I → ℂ[X])
    (hQ : ∀ i j, IsPadicRankLPolynomial F ψ' ν'.val
      (smoothContragredient
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n i))
          (s i) (δ i).representation))
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n j))
        (s j) (δ j).representation) (Q i j))
    (hprod : P = ∏ i, ∏ j, Q i j) :
    IsCenteredSegmentFamilyLProduct F d s P
      (fun i j => (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data.reciprocal) := by
  have ht : P = ∏ i, ∏ j, Q j i := hprod.trans (Finset.prod_comm)
  have h := centeredSegmentFamilyLProduct_of_certifiedProduct F ψ' ν' d hH hEq s
    (fun i j => Q j i)
    (fun i j => (isPadicRankLPolynomial_comm _ _ _).mp (hQ j i)) ht
  have hb :
      (fun i j => (centeredSegmentBaseEulerFamily hEq ψ' ν' d i j).data.reciprocal) =
        (fun i j => (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data.reciprocal) := by
    funext i j
    rw [centeredSegmentBaseEulerFamily_data_character_independent F ψ ν ψ' ν' d hEq]
  rw [hb] at h
  exact h

/-- Admissible biduality turns the actual smooth dual of the original mixed
pair into a reversed mixed pair before transposing the finite product. -/
theorem centeredSegmentFamilyLProduct_of_dualCertifiedProduct [Fintype I]
    (hH : SegmentHeadLFactorStatement.{uF, max uF uV, max uF uV})
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    (hadm : ∀ i, IsAdmissible (δ i).representation)
    (s : I → ℝ) {P : ℂ[X]} (Q : I → I → ℂ[X])
    (hQ : ∀ i j, IsPadicRankLPolynomial F ψ' ν'.val
      (smoothContragredient
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n i))
          (s i) (δ i).representation))
      (smoothContragredient (smoothContragredient
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n j))
          (s j) (δ j).representation))) (Q i j))
    (hprod : P = ∏ i, ∏ j, Q i j) :
    IsCenteredSegmentFamilyLProduct F d s P
      (fun i j => (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data.reciprocal) := by
  apply centeredSegmentFamilyLProduct_of_reverseCertifiedProduct F ψ ν ψ' ν' d
    hH hEq s Q ?_ hprod
  intro i j
  let A := F.canonicalTopologicalData.segmentFactor (δ j) (s j)
  have ha : A.IsAdmissible :=
    (Langlands.isAdmissible_twist_iff _ _
      (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter (n j) (s j))).mpr
      (hadm j)
  let e := SmoothRep.equivOfIso
    (SmoothRep.bidualIso (compactOpen_cofinal F F.canonicalTopologicalData (n j)) A ha)
  exact (IsPadicRankLPolynomial.congr_equiv (Representation.Equiv.refl _) e).mpr (hQ i j)

/-- Assemble the two Appendix L-products from the actual original and smooth
dual pair certificates and their exact polynomial products. -/
theorem centeredSegmentFamilyLProductPair_of_certifiedProducts [Fintype I]
    (hH : SegmentHeadLFactorStatement.{uF, max uF uV, max uF uV})
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    (hadm : ∀ i, IsAdmissible (δ i).representation)
    (s : I → ℝ) {P Pdual : ℂ[X]} (Q Qdual : I → I → ℂ[X])
    (hQ : ∀ i j, IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n i))
        (s i) (δ i).representation)
      (smoothContragredient
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n j))
          (s j) (δ j).representation)) (Q i j))
    (hQdual : ∀ i j, IsPadicRankLPolynomial F ψ' ν'.val
      (smoothContragredient
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n i))
          (s i) (δ i).representation))
      (smoothContragredient (smoothContragredient
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n j))
          (s j) (δ j).representation))) (Qdual i j))
    (hprod : P = ∏ i, ∏ j, Q i j)
    (hprodDual : Pdual = ∏ i, ∏ j, Qdual i j) :
    IsCenteredSegmentFamilyLProductPair F d s P Pdual
      (fun i j => (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data.reciprocal) :=
  ⟨centeredSegmentFamilyLProduct_of_certifiedProduct F ψ ν d hH hEq s Q hQ hprod,
    centeredSegmentFamilyLProduct_of_dualCertifiedProduct F ψ ν ψ' ν' d
      hH hEq hadm s Qdual hQdual hprodDual⟩

/-- The pointwise epsilon-times-reflected-L-over-L expression is the Appendix
gamma function once the two actual L-products have been identified. -/
theorem IsCenteredSegmentFamilyLProductPair.gammaExpression [Fintype I]
    {s : I → ℝ} {P Pdual : ℂ[X]} {base : I → I → ℂ → ℂ}
    (h : IsCenteredSegmentFamilyLProductPair F d s P Pdual base)
    (epsilon : ℂ → ℂ) :
    (fun z => epsilon z *
      (Pdual.eval (spectralPoint F.canonicalTopologicalData.residueCardinality (1 - z)))⁻¹ /
      (P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality z))⁻¹) =
      Global.PoleComparison.blockGamma (fun i => (d i).segment.length - 1) s base epsilon := by
  funext z
  rw [h.1 z, h.2 (1 - z)]
  rfl

end Langlands.RankinSelberg
