import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedDualModel
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalFixedDual
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalOriginal
import Langlands.Representation.RankinSelberg.HaarSymmetriesProof

/-! # The actual leading-sign and Weyl transport of the dual Fourier integral -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NNReal

namespace Langlands.Conductor

open GeneralLinear
universe uK
variable {K : Type uK} [Field K]

/-- Integral conjugation preserves the actual image of the reduction kernel. -/
theorem conjugate_mem_principalCongruenceSubgroup
    (O : Subring K) (n : ℕ) (I : Ideal O)
    {h k : Langlands.GeneralLinear (n + 1) K}
    (hh : h ∈ integralSubgroup O n) (hk : k ∈ principalCongruenceSubgroup O n I) :
    h * k * h⁻¹ ∈ principalCongruenceSubgroup O n I := by
  obtain ⟨h₀, rfl⟩ := hh
  obtain ⟨k₀, hk₀, rfl⟩ := hk
  refine ⟨h₀ * k₀ * h₀⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  change Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) k₀ = 1 at hk₀
  change Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) (h₀ * k₀ * h₀⁻¹) = 1
  simp only [map_mul, map_inv, hk₀, mul_one, mul_inv_cancel]

/-- The explicit leading sign has an integral invertible lift over every subring. -/
theorem rankOneWeylLeadingSign_mem_integralSubgroup (O : Subring K) (n : ℕ) :
    RankinSelberg.rankOneWeylLeadingSign n ∈ integralSubgroup O n := by
  rw [mem_integralSubgroup, RankinSelberg.rankOneWeylLeadingSign_inv]
  have h : ∀ i j, RankinSelberg.rankOneWeylLeadingSign (K := K) n i j ∈ O := by
    intro i j
    rw [RankinSelberg.rankOneWeylLeadingSign_val]
    by_cases hij : i = j
    · subst j
      by_cases hi : i = 0 <;> simp [hi]
    · simp [hij]
  exact ⟨h, h⟩

/-- Signed duality preserves precisely the same principal level. -/
theorem rankOneSignedDualFunction_principalFixed
    [ValuativeRel K] [TopologicalSpace K] [IsTopologicalRing K]
    (n a : ℕ) (W : Langlands.GeneralLinear (n + 1) K → ℂ)
    (hW : ∀ k ∈ principalLevelSubgroup K n a, ∀ g, W (g * k) = W g) :
    ∀ k ∈ principalLevelSubgroup K n a, ∀ g,
      RankinSelberg.rankOneSignedDualFunction n W (g * k) =
        RankinSelberg.rankOneSignedDualFunction n W g := by
  intro k hk g
  have hm := conjugate_mem_principalCongruenceSubgroup
    (ValuativeRel.valuation K).integer n _
    (rankOneWeylLeadingSign_mem_integralSubgroup _ n)
    (inverseTranspose_mem_principalLevelSubgroup K n a hk)
  rw [RankinSelberg.rankOneWeylLeadingSign_inv] at hm
  have he : (RankinSelberg.rankOneSignedWeyl n * inverseTranspose (n + 1) K g *
      RankinSelberg.rankOneWeylLeadingSign n) *
      (RankinSelberg.rankOneWeylLeadingSign n * inverseTranspose (n + 1) K k *
        RankinSelberg.rankOneWeylLeadingSign n) =
    RankinSelberg.rankOneSignedWeyl n * inverseTranspose (n + 1) K (g * k) *
      RankinSelberg.rankOneWeylLeadingSign n := by
    simp only [map_mul, mul_assoc]
    rw [← mul_assoc (RankinSelberg.rankOneWeylLeadingSign n),
      RankinSelberg.rankOneWeylLeadingSign_mul_self, one_mul]
  exact (congrArg W he).symm.trans (hW _ hm _)

end Langlands.Conductor

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear Whittaker Conductor RankOneBox
universe uF
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance signedDualTransportTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance signedDualTransportValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance signedDualTransportLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance signedDualTransportT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance signedDualTransportScalarMeasurable : MeasurableSpace F.Carrier := borel _
local instance signedDualTransportScalarBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance signedDualTransportGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance signedDualTransportGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "𝓛" => F.canonicalTopologicalData.additiveLattice

/-- The full original box test is invariant under its leading-column sign. -/
theorem boxLatticeTest_rightLeadingSign (n : ℕ) (A q : ℤ) (a : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    boxLatticeTest F A q a (M * (rankOneWeylLeadingSign n).val) =
      boxLatticeTest F A q a M := by
  have hf : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier,
      X ∈ box F A q a → X * (rankOneWeylLeadingSign n).val ∈ box F A q a := by
    intro X hX
    rw [mem_box_iff] at hX ⊢
    simp only [rankOneWeylLeadingSign_val, Matrix.mul_diagonal]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [ite_true, mul_neg_one] using (𝓛 A).neg_mem hX.1
    · intro j hj
      simpa only [ite_eq_right hj, mul_one] using hX.2.1 j hj
    · intro i hi j
      by_cases hj : j = 0
      · subst j
        have hz : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i 0 = 0 := by
          simp [hi]
        simp only [ite_true, mul_neg_one, hz, sub_zero]
        rw [levelSet_eq_additiveLattice] at hX ⊢
        exact (𝓛 (-(a : ℤ))).neg_mem (by simpa only [hz, sub_zero, SetLike.mem_coe] using hX.2.2 i hi 0)
      · simpa only [ite_eq_right hj, mul_one] using hX.2.2 i hi j
  have he : M * (rankOneWeylLeadingSign n).val ∈ box F A q a ↔ M ∈ box F A q a := by
    refine ⟨fun h => ?_, hf M⟩
    have h' := hf _ h
    simpa only [Matrix.mul_assoc, ← Units.val_mul, rankOneWeylLeadingSign_mul_self,
      Units.val_one, Matrix.mul_one] using h'
  simp only [boxLatticeTest_apply]
  by_cases hM : M ∈ box F A q a
  · rw [Set.indicator_of_mem (he.mpr hM), Set.indicator_of_mem hM]
  · rw [Set.indicator_of_notMem (fun h => hM (he.mp h)), Set.indicator_of_notMem hM]

theorem determinantNorm_rankOneWeylLeadingSign (n : ℕ) :
    F.canonicalTopologicalData.determinantNorm (n + 1) (rankOneWeylLeadingSign n) = 1 := by
  apply F.canonicalTopologicalData.determinantNorm_eq_one_of_pow_eq_one _
    (by decide : 2 ≠ 0)
  rw [pow_two, rankOneWeylLeadingSign_mul_self]

theorem determinantNorm_rankOneSignedWeyl (n : ℕ) :
    F.canonicalTopologicalData.determinantNorm (n + 1) (rankOneSignedWeyl n) = 1 := by
  have hA : F.canonicalTopologicalData.determinantNorm (n + 1) (rankOneWeylAlternating n) = 1 := by
    apply F.canonicalTopologicalData.determinantNorm_eq_one_of_pow_eq_one _
      (by decide : 2 ≠ 0)
    rw [pow_two, rankOneWeylAlternating_mul_self]
  simp only [rankOneSignedWeyl, map_mul, hA,
    F.canonicalTopologicalData.determinantNorm_weylLong, one_mul]

/-- Every actual Fourier partner retains this exact leading-column symmetry. -/
theorem boxLatticeTest_fourier_rightLeadingSign
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ) (A q : ℤ) (a : ℕ) (ΦHat : GodementJacquet.MatrixTestFunction n F.Carrier)
    (hp : GodementJacquet.Padic.MatrixFourierPair F ψ ν (boxLatticeTest F A q a) ΦHat)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    ΦHat (M * (rankOneWeylLeadingSign n).val) = ΦHat M := by
  have h := GodementJacquet.padicMatrixFourierPair_leftRight_invariant F
    F.canonicalTopologicalData n ψ ν 1 (rankOneWeylLeadingSign n) (map_one _)
    (determinantNorm_rankOneWeylLeadingSign F n) _ ΦHat hp
    (by intro Y; simpa using boxLatticeTest_rightLeadingSign F n A q a Y) M
  simpa only [map_one, Units.val_one, Matrix.one_mul,
    inverseTranspose_rankOneWeylLeadingSign] using h

/-- The actual two-sided group substitution used in the signed Fourier passage. -/
def rankOneSignedDualHomeomorph (n : ℕ) :
    Langlands.GeneralLinear (n + 1) F.Carrier ≃ₜ Langlands.GeneralLinear (n + 1) F.Carrier :=
  (Homeomorph.mulLeft (rankOneSignedWeyl n)).trans
    (Homeomorph.mulRight (rankOneWeylLeadingSign n))

@[simp] theorem rankOneSignedDualHomeomorph_apply (n : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    rankOneSignedDualHomeomorph F n g = rankOneSignedWeyl n * g * rankOneWeylLeadingSign n := rfl

/-- Left and right Haar invariance give exact measure preservation. -/
theorem rankOneSignedDualHomeomorph_preserving (n : ℕ) :
    MeasurePreserving (rankOneSignedDualHomeomorph F n)
      (generalLinearHaar F.Carrier n) (generalLinearHaar F.Carrier n) :=
  (measurePreserving_mul_right (generalLinearHaar F.Carrier n) (rankOneWeylLeadingSign n)).comp
    (measurePreserving_mul_left (generalLinearHaar F.Carrier n) (rankOneSignedWeyl n))

/-- The complete integrands agree under the actual measure-preserving substitution. -/
theorem principalModelFourierIntegrand_signedDual_eq
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (m a : ℕ) (s : ℂ) (W : Langlands.GeneralLinear (m + 2) F.Carrier → ℂ)
    (ΦHat : GodementJacquet.MatrixTestFunction (m + 1) F.Carrier)
    (hp : GodementJacquet.Padic.MatrixFourierPair F ψ ν
      (boxLatticeTest F (F.canonicalTopologicalData.additiveConductor ψ + a)
        (F.canonicalTopologicalData.additiveConductor ψ) a) ΦHat)
    (h : Langlands.GeneralLinear (m + 2) F.Carrier) :
    principalModelFourierIntegrand F ψ ν m a s (rankOneSignedDualFunction (m + 1) W) h =
      GodementJacquet.matrixIntegrand abv ΦHat s (GodementJacquet.coefficientIota W)
        (rankOneSignedDualHomeomorph F (m + 1) h) := by
  have hE : abv (rankOneWeylLeadingSign (m + 1)).val.det = 1 :=
    congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ))
      (determinantNorm_rankOneWeylLeadingSign F (m + 1))
  have hw : abv (rankOneSignedWeyl (m + 1)).val.det = 1 :=
    congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ))
      (determinantNorm_rankOneSignedWeyl F (m + 1))
  have hweightE : determinantWeight abv (rankOneWeylLeadingSign (m + 1)) s = 1 := by
    simp only [determinantWeight, hE, Complex.ofReal_one, Complex.one_cpow]
  have hweightw : determinantWeight abv (rankOneSignedWeyl (m + 1)) s = 1 := by
    simp only [determinantWeight, hw, Complex.ofReal_one, Complex.one_cpow]
  simp only [principalModelFourierIntegrand, rankOneSignedDualHomeomorph_apply,
    GodementJacquet.matrixIntegrand, rankOneSignedDualFunction_eq_iota,
    determinantWeight_mul, hweightE, hweightw, one_mul, mul_one, Units.val_mul,
    boxLatticeTest_fourier_rightLeadingSign F ψ ν _ _ _ _ ΦHat hp,
    ← (hp _).2]
  ring

/-- Genuine raw inverse-transpose convergence is equivalent to convergence of
its signed same-character Fourier restriction. -/
theorem integrable_principalModelFourierIntegrand_signedDual_iff
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (m a : ℕ) (s : ℂ) (W : Langlands.GeneralLinear (m + 2) F.Carrier → ℂ)
    (ΦHat : GodementJacquet.MatrixTestFunction (m + 1) F.Carrier)
    (hp : GodementJacquet.Padic.MatrixFourierPair F ψ ν
      (boxLatticeTest F (F.canonicalTopologicalData.additiveConductor ψ + a)
        (F.canonicalTopologicalData.additiveConductor ψ) a) ΦHat) :
    Integrable (principalModelFourierIntegrand F ψ ν m a s (rankOneSignedDualFunction (m + 1) W))
      (generalLinearHaar F.Carrier (m + 1)) ↔
    Integrable (GodementJacquet.matrixIntegrand abv ΦHat s (GodementJacquet.coefficientIota W))
      (generalLinearHaar F.Carrier (m + 1)) := by
  have he : principalModelFourierIntegrand F ψ ν m a s (rankOneSignedDualFunction (m + 1) W) =
      (GodementJacquet.matrixIntegrand abv ΦHat s (GodementJacquet.coefficientIota W)) ∘
        rankOneSignedDualHomeomorph F (m + 1) :=
    funext (principalModelFourierIntegrand_signedDual_eq F ψ ν m a s W ΦHat hp)
  rw [he]
  exact (rankOneSignedDualHomeomorph_preserving F (m + 1)).integrable_comp_emb
    (rankOneSignedDualHomeomorph F (m + 1)).measurableEmbedding

/-- This substitution contributes no scalar to the actual dual matrix value. -/
theorem integral_principalModelFourierIntegrand_signedDual
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (m a : ℕ) (s : ℂ) (W : Langlands.GeneralLinear (m + 2) F.Carrier → ℂ)
    (ΦHat : GodementJacquet.MatrixTestFunction (m + 1) F.Carrier)
    (hp : GodementJacquet.Padic.MatrixFourierPair F ψ ν
      (boxLatticeTest F (F.canonicalTopologicalData.additiveConductor ψ + a)
        (F.canonicalTopologicalData.additiveConductor ψ) a) ΦHat) :
    (∫ h, principalModelFourierIntegrand F ψ ν m a s (rankOneSignedDualFunction (m + 1) W) h
      ∂generalLinearHaar F.Carrier (m + 1)) =
    GodementJacquet.matrixIntegral abv (generalLinearHaar F.Carrier (m + 1)) ΦHat s
      (GodementJacquet.coefficientIota W) := by
  simp_rw [principalModelFourierIntegrand_signedDual_eq F ψ ν m a s W ΦHat hp]
  exact (rankOneSignedDualHomeomorph_preserving F (m + 1)).integral_comp
    (rankOneSignedDualHomeomorph F (m + 1)).measurableEmbedding _

end Langlands.RankinSelberg
