import Langlands.Representation.RankinSelberg.TemperedLFactorGamma
import Langlands.Representation.Parabolic.InverseTransposeProductProof
import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualDuality

/-! Certified dual polynomials on the actual inverse-transpose inductions. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

namespace TemperedLFactorDual

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {r t k l : ℕ} (m : Fin k → ℕ) (n : Fin l → ℕ)
  (hm : ∑ i, (m i + 1) = r + 1) (hn : ∑ j, (n j + 1) = t + 1)
  {V : Fin k → Type uV} [haddV : ∀ i, AddCommGroup (V i)] [hmodV : ∀ i, Module ℂ (V i)]
  {W : Fin l → Type uW} [haddW : ∀ j, AddCommGroup (W j)] [hmodW : ∀ j, Module ℂ (W j)]
  (π : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (V i))
  (σ : ∀ j, Representation ℂ (Langlands.GeneralLinear (n j + 1) F.Carrier) (W j))

local instance canonicalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance canonicalValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance canonicalLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- L-certificates for actual pulled-back inductions and block pairs, with a
normalized residual for the double product. The same supplied measure is used. -/
structure DualTwoFamilyLPolynomialData where
  inducedPolynomial : ℂ[X]
  blockPolynomial : Fin k → Fin l → ℂ[X]
  induced_spec : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
    (inverseTransposePullback
      (F.canonicalNormalizedProductInduced (succBlockShape m hm) π))
    (inverseTransposePullback
      (F.canonicalNormalizedProductInduced (succBlockShape n hn) σ)) inducedPolynomial
  block_spec : ∀ i j, IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
    (inverseTransposePullback (π i)) (inverseTransposePullback (σ j)) (blockPolynomial i j)
  quotient : TemperedLFactorAlgebra.NormalizedPolynomialQuotient
    inducedPolynomial (∏ i, ∏ j, blockPolynomial i j)

/-- Apply the two-family construction to the reversed dual blocks and transport
the resulting certificates along the published actual induction equivalences. -/
theorem nonempty_dualTwoFamilyLPolynomialData
    (hπ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (π i))
    (hσ : ∀ j, IsOfWhittakerType (n j) (standardCharacter ψ (n j)) (σ j)) :
    Nonempty (DualTwoFamilyLPolynomialData F ψ ν m n hm hn π σ) := by
  classical
  let : ∀ i : Fin k, AddCommGroup (V i.rev) := fun i => haddV i.rev
  let : ∀ i : Fin k, Module ℂ (V i.rev) := fun i => hmodV i.rev
  let : ∀ j : Fin l, AddCommGroup (W j.rev) := fun j => haddW j.rev
  let : ∀ j : Fin l, Module ℂ (W j.rev) := fun j => hmodW j.rev
  let hmD : ∑ i : Fin k, (m i.rev + 1) = r + 1 :=
    (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans hm
  let hnD : ∑ j : Fin l, (n j.rev + 1) = t + 1 :=
    (Equiv.sum_comp Fin.revPerm (fun j => n j + 1)).trans hn
  let πD := fun i : Fin k => inverseTransposePullback (π i.rev)
  let σD := fun j : Fin l => inverseTransposePullback (σ j.rev)
  have hπD (i) : IsOfWhittakerType (m i.rev)
      (standardCharacter (ψ.scale (-1)) (m i.rev)) (πD i) :=
    isOfWhittakerType_firstDual ψ (π i.rev) (hπ i.rev)
  have hσD (j) : IsOfWhittakerType (n j.rev)
      (standardCharacter (ψ.scale (-1)) (n j.rev)) (σD j) :=
    isOfWhittakerType_firstDual ψ (σ j.rev) (hσ j.rev)
  let νD := DominantRankTransport.negatedSelfDualHaar F ψ ν
  let d := TemperedLFactorDivisibility.twoFamilyLPolynomialData F (ψ.scale (-1)) νD
    (fun i => m i.rev) (fun j => n j.rev) hmD hnD πD σD hπD hσD
  obtain ⟨eπ⟩ := Parabolic.normalizedProductInverseTranspose F.canonicalTopologicalData
    (r + 1) (Nat.succ_pos r) (succBlockShape m hm) V π (fun i => (hπ i).1.1)
  obtain ⟨eσ⟩ := Parabolic.normalizedProductInverseTranspose F.canonicalTopologicalData
    (t + 1) (Nat.succ_pos t) (succBlockShape n hn) W σ (fun j => (hσ j).1.1)
  have hP : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
      (inverseTransposePullback
        (F.canonicalNormalizedProductInduced (succBlockShape m hm) π))
      (inverseTransposePullback
        (F.canonicalNormalizedProductInduced (succBlockShape n hn) σ)) d.inducedPolynomial :=
    (IsPadicSymmetricLPolynomial.congr_equiv eπ eσ).mpr d.induced_spec
  have hQ (i j) : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
      (inverseTransposePullback (π i)) (inverseTransposePullback (σ j))
        (d.blockPolynomial i.rev j.rev) := by
    obtain ⟨i, rfl⟩ := Fin.rev_surjective i
    obtain ⟨j, rfl⟩ := Fin.rev_surjective j
    simpa only [Fin.rev_rev, πD, σD, νD,
      DominantRankTransport.negatedSelfDualHaar_val] using d.block_spec i j
  have hprod : (∏ i : Fin k, ∏ j : Fin l, d.blockPolynomial i.rev j.rev) =
      ∏ i, ∏ j, d.blockPolynomial i j := by
    calc
      _ = ∏ i : Fin k, ∏ j : Fin l, d.blockPolynomial i j.rev :=
        Equiv.prod_comp Fin.revPerm
          (fun i : Fin k => ∏ j : Fin l, d.blockPolynomial i j.rev)
      _ = _ := Finset.prod_congr rfl fun i _ =>
        Equiv.prod_comp Fin.revPerm (d.blockPolynomial i)
  exact ⟨{
    inducedPolynomial := d.inducedPolynomial
    blockPolynomial := fun i j => d.blockPolynomial i.rev j.rev
    induced_spec := hP
    block_spec := hQ
    quotient := {
      polynomial := d.quotient.polynomial
      coeff_zero := d.quotient.coeff_zero
      factorization := hprod.trans d.quotient.factorization } }⟩

end TemperedLFactorDual

end Langlands.RankinSelberg
