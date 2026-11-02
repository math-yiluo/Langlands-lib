import Langlands.Representation.RankinSelberg.TemperedLFactorDual
import Langlands.Representation.Classification.InverseTransposeAnalyticProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof

/-! Product equality from original and dual divisibility and block pole bounds. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

namespace TemperedLFactorProduct

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {r t k l : ℕ} (m : Fin k → ℕ) (n : Fin l → ℕ)
  (hm : ∑ i, (m i + 1) = r + 1) (hn : ∑ j, (n j + 1) = t + 1)
  {V : Fin k → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {W : Fin l → Type uW} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
  (π : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (V i))
  (σ : ∀ j, Representation ℂ (Langlands.GeneralLinear (n j + 1) F.Carrier) (W j))

local instance canonicalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance canonicalValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance canonicalLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- Certified polynomials for the actual inductions and their block pairs,
with product equality and nonvanishing in the open unit disk. -/
structure ProductLPolynomialData where
  inducedPolynomial : ℂ[X]
  blockPolynomial : Fin k → Fin l → ℂ[X]
  induced_spec : IsPadicSymmetricLPolynomial F ψ ν.val
    (F.canonicalNormalizedProductInduced (succBlockShape m hm) π)
    (F.canonicalNormalizedProductInduced (succBlockShape n hn) σ) inducedPolynomial
  block_spec : ∀ i j, IsPadicSymmetricLPolynomial F ψ ν.val
    (π i) (σ j) (blockPolynomial i j)
  product_eq : inducedPolynomial = ∏ i, ∏ j, blockPolynomial i j
  poleFree : ∀ z : ℂ, ‖z‖ < 1 → inducedPolynomial.eval z ≠ 0

/-- Full block Whittaker type and the closed square-integrable pole premise
reduce the original and dual residuals to one by reflection rigidity. -/
theorem nonempty_productLPolynomialData
    (hPole : SquareIntegrablePoleFreeStatement.{uF, uV, uW})
    (hπ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (π i))
    (hσ : ∀ j, IsOfWhittakerType (n j) (standardCharacter ψ (n j)) (σ j))
    (hiπ : ∀ i, Representation.IsIrreducible (π i))
    (hsπ : ∀ i, F.canonicalTopologicalData.IsSquareIntegrable (π i))
    (hiσ : ∀ j, Representation.IsIrreducible (σ j))
    (hsσ : ∀ j, F.canonicalTopologicalData.IsSquareIntegrable (σ j)) :
    Nonempty (ProductLPolynomialData F ψ ν m n hm hn π σ) := by
  classical
  let d := TemperedLFactorDivisibility.twoFamilyLPolynomialData
    F ψ ν m n hm hn π σ hπ hσ
  obtain ⟨e⟩ := TemperedLFactorDual.nonempty_dualTwoFamilyLPolynomialData
    F ψ ν m n hm hn π σ hπ hσ
  obtain ⟨g⟩ := TemperedLFactorGamma.nonempty_reflectedRatioData
    F ψ ν m n hm hn π σ hπ hσ
    d.inducedPolynomial e.inducedPolynomial d.blockPolynomial e.blockPolynomial
    d.induced_spec d.block_spec e.induced_spec e.block_spec
  have hiπD (i) : Representation.IsIrreducible (inverseTransposePullback (π i)) :=
    CuspidalSupport.isIrreducible_comp_of_surjective (π i) (hρ := hiπ i)
      (GeneralLinear.inverseTranspose (m i + 1) F.Carrier).toMonoidHom
      (GeneralLinear.inverseTranspose (m i + 1) F.Carrier).surjective
  have hiσD (j) : Representation.IsIrreducible (inverseTransposePullback (σ j)) :=
    CuspidalSupport.isIrreducible_comp_of_surjective (σ j) (hρ := hiσ j)
      (GeneralLinear.inverseTranspose (n j + 1) F.Carrier).toMonoidHom
      (GeneralLinear.inverseTranspose (n j + 1) F.Carrier).surjective
  have hsπD (i) : F.canonicalTopologicalData.IsSquareIntegrable
      (inverseTransposePullback (π i)) :=
    F.canonicalTopologicalData.isSquareIntegrable_comp_continuousMulEquiv (π i)
      (F.canonicalTopologicalData.generalLinearInverseTranspose (m i + 1)) (hsπ i)
  have hsσD (j) : F.canonicalTopologicalData.IsSquareIntegrable
      (inverseTransposePullback (σ j)) :=
    F.canonicalTopologicalData.isSquareIntegrable_comp_continuousMulEquiv (σ j)
      (F.canonicalTopologicalData.generalLinearInverseTranspose (n j + 1)) (hsσ j)
  have hB : ∀ z : ℂ, ‖z‖ < 1 →
      (∏ i, ∏ j, d.blockPolynomial i j).eval z ≠ 0 :=
    TemperedLFactorAlgebra.doubleProduct_poleFree fun i j =>
      TemperedLFactorAlgebra.certifiedSquareIntegrable_poleFree hPole
        (hiπ i) (hsπ i) (hiσ j) (hsσ j) (d.block_spec i j)
  have hBD : ∀ z : ℂ, ‖z‖ < 1 →
      (∏ i, ∏ j, e.blockPolynomial i j).eval z ≠ 0 :=
    TemperedLFactorAlgebra.doubleProduct_poleFree fun i j =>
      TemperedLFactorAlgebra.certifiedSquareIntegrable_poleFree hPole
        (ν := DominantRankTransport.negatedSelfDualHaar F ψ ν)
        (hiπD i) (hsπD i) (hiσD j) (hsσD j) (e.block_spec i j)
  have hP : d.inducedPolynomial ≠ 0 := by
    intro hzero
    have hc := d.induced_spec.coeff_zero
    simp only [hzero, coeff_zero, zero_ne_one] at hc
  have hPD : e.inducedPolynomial ≠ 0 := by
    intro hzero
    have hc := e.induced_spec.coeff_zero
    simp only [hzero, coeff_zero, zero_ne_one] at hc
  have hBDne : (∏ i, ∏ j, e.blockPolynomial i j) ≠ 0 := by
    intro hzero
    have hz := hBD 0 (by simp)
    exact hz (by rw [hzero, eval_zero])
  have hidentity := TemperedLFactorAlgebra.reflected_identity_of_quotient_ratio
    (LocalFactor.residueReflection F) g.coefficient g.exponent hP hPD hBDne
    d.quotient.factorization e.quotient.factorization g.ratio
  obtain ⟨hprod, _, hpole⟩ := TemperedLFactorAlgebra.eq_of_reflected_quotients
    (LocalFactor.residueReflection F) g.coefficient g.exponent
    (TemperedLFactorAlgebra.norm_residueReflection_lt_one F)
    d.quotient.coeff_zero e.quotient.coeff_zero
    d.quotient.factorization e.quotient.factorization hB hBD hidentity
  exact ⟨{
    inducedPolynomial := d.inducedPolynomial
    blockPolynomial := d.blockPolynomial
    induced_spec := d.induced_spec
    block_spec := d.block_spec
    product_eq := hprod
    poleFree := hpole }⟩

end TemperedLFactorProduct

end Langlands.RankinSelberg
