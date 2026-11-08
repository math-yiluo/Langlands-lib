import Langlands.Representation.RankinSelberg.LanglandsTypeTailDivisibility
import Langlands.Representation.RankinSelberg.SegmentPairPoleOrder
import Langlands.Representation.RankinSelberg.TemperedLFactorGamma
import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualDuality
import Langlands.Representation.Classification.LanglandsInverseTransposeDatum

/-! Reflected residuals on the genuine original and reversed Langlands data. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear Polynomial
open PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology;
    UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

local instance langlandsTypeReflectionDataTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance canonicalValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance canonicalLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

variable {F ψ ν}

/-- Every arbitrary-rank polynomial certificate has normalized constant term. -/
theorem IsPadicRankLPolynomial.coeff_zero
    {n t : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W}
    {P : ℂ[X]} (hP : IsPadicRankLPolynomial F ψ ν.val π σ P) :
    P.coeff 0 = 1 := by
  cases n with
  | zero => exact hP.elim
  | succ n => cases t with
    | zero => exact hP.elim
    | succ t => exact IsPadicSymmetricLPolynomial.coeff_zero hP

variable (F ψ ν) {r t : ℕ}
  (d : TemperedLanglandsDatum.{uV,uF} F.canonicalTopologicalData (r + 1))
  (e : TemperedLanglandsDatum.{uW,uF} F.canonicalTopologicalData (t + 1))

set_option maxHeartbeats 800000 in
/-- Certificates for the genuine reversed data give the reflected gamma ratio
with the complete original and dual block products. -/
theorem nonempty_langlandsTypeReflectedRatioData
    (c : LanglandsTypeLPolynomialData F ψ ν d e)
    (cD : LanglandsTypeLPolynomialData F (ψ.scale (-1))
      (DominantRankTransport.negatedSelfDualHaar F ψ ν)
      d.inverseTranspose e.inverseTranspose) :
    Nonempty (TemperedLFactorGamma.ReflectedRatioData
      (LocalFactor.residueReflection F) c.inducedPolynomial cD.inducedPolynomial
      (∏ i, ∏ j, c.blockPolynomial i j) (∏ i, ∏ j, cD.blockPolynomial i j)) := by
  have hPD := (IsPadicSymmetricLPolynomial.congr_equiv
    (d.inverseTransposeStandardModuleEquiv (Nat.succ_pos r))
    (e.inverseTransposeStandardModuleEquiv (Nat.succ_pos t))).mpr cD.induced_spec
  have hQD (i : Fin d.shape.length) (j : Fin e.shape.length) :
      IsPadicRankLPolynomial F (ψ.scale (-1)) ν.val
        ((F.canonicalTopologicalData.twistedBlocks d.shape d.blocks d.exponent i).representation.comp
          (GeneralLinear.inverseTranspose (d.shape.size i) F.Carrier).toMonoidHom)
        ((F.canonicalTopologicalData.twistedBlocks e.shape e.blocks e.exponent j).representation.comp
          (GeneralLinear.inverseTranspose (e.shape.size j) F.Carrier).toMonoidHom)
        (cD.blockPolynomial i.rev j.rev) := by
    obtain ⟨i, rfl⟩ := Fin.rev_surjective i
    obtain ⟨j, rfl⟩ := Fin.rev_surjective j
    apply (IsPadicRankLPolynomial.congr_equiv
      (SmoothRep.equivOfIso (d.inverseTransposeTwistedBlockIso i))
      (SmoothRep.equivOfIso (e.inverseTransposeTwistedBlockIso j))).mpr
    have h := cD.block_spec i j
    change IsPadicRankLPolynomial F (ψ.scale (-1)) ν.val
      (F.canonicalTopologicalData.twistedBlocks d.inverseTranspose.shape
        d.inverseTranspose.blocks d.inverseTranspose.exponent i).representation
      (F.canonicalTopologicalData.twistedBlocks e.inverseTranspose.shape
        e.inverseTranspose.blocks e.inverseTranspose.exponent j).representation
      (cD.blockPolynomial i j) at h
    dsimp only [TemperedLanglandsDatum.inverseTranspose, BlockShape.reverse] at h ⊢
    simpa only [Fin.rev_rev] using h
  have hprod : (∏ i : Fin d.shape.length, ∏ j : Fin e.shape.length,
      cD.blockPolynomial i.rev j.rev) =
      ∏ i, ∏ j, cD.blockPolynomial i j := by
    calc
      _ = ∏ i, ∏ j : Fin e.shape.length, cD.blockPolynomial i j.rev :=
        Equiv.prod_comp Fin.revPerm
          (fun i => ∏ j : Fin e.shape.length, cD.blockPolynomial i j.rev)
      _ = _ := Finset.prod_congr rfl fun i _ =>
        Equiv.prod_comp Fin.revPerm (cD.blockPolynomial i)
  rcases d with ⟨⟨k, size, pos, total⟩, π, hiπ, htπ, s, hs⟩
  rcases e with ⟨⟨l, size', pos', total'⟩, σ, hiσ, htσ, z, hz⟩
  obtain ⟨m, rfl⟩ : ∃ m : Fin k → ℕ, size = fun i => m i + 1 :=
    ⟨fun i => size i - 1, funext fun i => (Nat.sub_add_cancel (pos i)).symm⟩
  obtain ⟨n, rfl⟩ : ∃ n : Fin l → ℕ, size' = fun j => n j + 1 :=
    ⟨fun j => size' j - 1, funext fun j => (Nat.sub_add_cancel (pos' j)).symm⟩
  have hR := TemperedLFactorGamma.nonempty_reflectedRatioData F ψ ν m n total total'
    (fun i => (F.canonicalTopologicalData.segmentFactor (π i) (s i)).representation)
    (fun j => (F.canonicalTopologicalData.segmentFactor (σ j) (z j)).representation)
    (fun i => analyticTemperedRealTwistWhittakerType F ψ
      (π i).representation (hiπ i) (htπ i) (s i))
    (fun j => analyticTemperedRealTwistWhittakerType F ψ
      (σ j).representation (hiσ j) (htσ j) (z j))
    c.inducedPolynomial cD.inducedPolynomial c.blockPolynomial
    (fun i j => cD.blockPolynomial i.rev j.rev) c.induced_spec c.block_spec hPD hQD
  simpa only [hprod] using hR

/-- Original and reversed certified polynomial data, together with the
reciprocal-reflection identity for their normalized residuals. -/
structure LanglandsTypeReflectionData where
  original : LanglandsTypeLPolynomialData F ψ ν d e
  dual : LanglandsTypeLPolynomialData F (ψ.scale (-1))
    (DominantRankTransport.negatedSelfDualHaar F ψ ν)
    d.inverseTranspose e.inverseTranspose
  coefficient : ℂˣ
  exponent : ℤ
  identity : algebraMap ℂ[X] (RatFunc ℂ) original.quotient.polynomial =
    (RatFunc.C (coefficient : ℂ) * (RatFunc.X : RatFunc ℂ) ^ exponent) *
      LocalFactor.RationalReflection.subst (LocalFactor.residueReflection F)
        (algebraMap ℂ[X] (RatFunc ℂ) dual.quotient.polynomial)

/-- Derive the reflected residual identity on the unchanged genuine data. -/
def langlandsTypeReflectionData : LanglandsTypeReflectionData F ψ ν d e := by
  let c := langlandsTypeLPolynomialData F ψ ν d e
  let cD := langlandsTypeLPolynomialData F (ψ.scale (-1))
    (DominantRankTransport.negatedSelfDualHaar F ψ ν)
    d.inverseTranspose e.inverseTranspose
  let R := Classical.choice (nonempty_langlandsTypeReflectedRatioData F ψ ν d e c cD)
  refine {
    original := c
    dual := cD
    coefficient := R.coefficient
    exponent := R.exponent
    identity := ?_ }
  have hP : c.inducedPolynomial ≠ 0 :=
    fun h => by simpa [h] using c.induced_spec.coeff_zero
  have hPD : cD.inducedPolynomial ≠ 0 :=
    fun h => by simpa [h] using cD.induced_spec.coeff_zero
  have hBD : (∏ i, ∏ j, cD.blockPolynomial i j) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact fun h => by simpa [h] using (cD.block_spec i j).coeff_zero
  exact TemperedLFactorAlgebra.reflected_identity_of_quotient_ratio
    (LocalFactor.residueReflection F) R.coefficient R.exponent hP hPD hBD
    c.quotient.factorization cD.quotient.factorization R.ratio

end Langlands.RankinSelberg
