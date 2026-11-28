import Langlands.BaseChange.RegularTransferCharts
import Langlands.JacquetLanglands.DivisionRegularTransferStatement
import Langlands.JacquetLanglands.RegularDivisionOrbitalProfile

/-! # Regular orbital-integral transfer from division units to the general linear group -/

noncomputable section

namespace Langlands.JacquetLanglands

open Set MeasureTheory MeasureTheory.Measure _root_.Topology
open Langlands.BaseChange Langlands.CentralSimple Langlands.HarmonicAnalysis
open Langlands.QuotientIntegration Langlands.TraceFormula
open Langlands.BaseChange.SigmaLiftCharacterIdentity
  (coefficients coefficients_conj continuous_coefficients)
open Langlands.Topology (HasCompactOpenNeighborhoodBasis IsLocallyProfinite
  hasCompactOpenNeighborhoodBasis_of_mathlib isLocallyProfinite_of_mathlib)
open scoped NNReal

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u

set_option maxHeartbeats 900000 in
/-- Every regular-supported Schwartz–Bruhat function on the division units has a matching
function supported on the regular elliptic locus of the split general linear group. -/
theorem divisionRegularTransfer : DivisionRegularTransferStatement.{u} := by
  intro F _ _ _ _ _ D _ _ _ _ _ _ n hn
  have hd : reducedDegree F D = n := by rw [reducedDegree, hn, pow_two, Nat.sqrt_eq]
  subst n
  let d := reducedDegree F D
  let G := GeneralLinear d F
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace Dˣ := borel Dˣ
  let : BorelSpace Dˣ := ⟨rfl⟩
  let : IsTopologicalRing D := isTopologicalRing F D
  intro μ _ μ' _ f' hf'
  let : T2Space F := LocalFieldTopology.t2Space F
  let : SecondCountableTopology F := LocalFieldTopology.secondCountableTopology F
  let : TotallyDisconnectedSpace F := LocalFieldTopology.totallyDisconnectedSpace F
  let : T2Space G := LocalFieldTopology.generalLinear_t2Space F d
  let : LocallyCompactSpace G := LocalFieldTopology.generalLinear_locallyCompactSpace F d
  let : SecondCountableTopology G := LocalFieldTopology.generalLinear_secondCountableTopology F d
  let : TotallyDisconnectedSpace G := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F d
  let : T2Space Dˣ := units_t2Space F D
  let : LocallyCompactSpace Dˣ := units_locallyCompactSpace F D
  let : SecondCountableTopology D :=
    (coordinateHomeomorph F D (Module.finBasis F D)).secondCountableTopology
  let : SecondCountableTopology Dˣ :=
    (finiteAlgebra_isOpenEmbedding_unitsVal (F := F) (A := D)).isEmbedding.secondCountableTopology
  let : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  let : IsArtinianRing F := IsArtinianRing.of_finite F F
  let : μ.IsMulRightInvariant := generalLinear_haar_rightInvariant F d μ
  let RF : Set G := {g | IsRegularSemisimple g}
  let RD : Set Dˣ := {a | IsRegular F D a}
  let pF (g : RF) := coefficients g.val
  let pD (a : RD) := divisionCoefficients F D a.val
  have hB : HasCompactOpenNeighborhoodBasis (Fin d → F) :=
    hasCompactOpenNeighborhoodBasis_of_mathlib
  have hG : IsLocallyProfinite G := isLocallyProfinite_of_mathlib
  obtain ⟨mF, hmF⟩ := RegularOrbitalMeasures.exists_isNormalized
    (θ := MonoidHom.id G) (μ := μ) (R := RF) continuous_id
    (fun g => regularCentralizer_hasLargestCompactOpenSubgroup F d g g.property)
    (fun g => glCentralizer_mul_comm g.property)
  have horbitF (g : RF) (x : G) :
      ∃ y : RF, (y : G) = twistedConj (MonoidHom.id G) x g ∧ pF y = pF g := by
    have hy : IsRegularSemisimple (x⁻¹ * g.val * x) := by
      unfold IsRegularSemisimple
      rw [charpoly_conj]
      exact g.property
    exact ⟨⟨x⁻¹ * g.val * x, hy⟩, rfl, coefficients_conj x g⟩
  have profF : RegularOrbitalProfileData mF pF := regularOrbitalProfilesFromCharts
    (MonoidHom.id G) continuous_id μ RF (isOpen_regularSemisimple d) pF
    (continuous_coefficients.comp continuous_subtype_val) hB horbitF
    (fun g => exists_ordinaryRegularOrbitalChart g) mF hmF
  obtain ⟨mD, hmD, profD⟩ := regularDivisionOrbitalProfile F D μ'
  obtain ⟨P, hP, hPval⟩ := profD.exists_profile (f := f') hf'
  have hPF : Function.support P ⊆ range pF := by
    intro b hb
    obtain ⟨a, rfl⟩ := hP hb
    obtain ⟨g, hg⟩ := exists_corresponds F D a a.property
    exact ⟨⟨g, hg.1.1⟩, (corresponds_iff_coefficients_eq F D a.property).mp hg⟩
  obtain ⟨A, _, hAval⟩ := profF.exists_test hG continuous_id P hPF
  let hS := Hecke.TestFunction.isClopen_support P
  let cut : LocallyConstant (Fin d → F) ℂ := LocallyConstant.charFn ℂ hS
  let f₀ (g : G) := cut (coefficients g) * A g
  have hf₀ : IsLocallyConstant f₀ :=
    (cut.isLocallyConstant.comp_continuous continuous_coefficients).comp₂ A.locallyConstant (· * ·)
  have hsupp : Function.support f₀ ⊆ Function.support A := by
    intro g hg hzero
    exact hg (show f₀ g = 0 by simp only [f₀, hzero, mul_zero])
  let f : SchwartzBruhat G := ⟨f₀, hf₀, A.hasCompactSupport.mono hsupp⟩
  have hf : IsEllipticSupported (f : G → ℂ) := by
    intro g hg
    have hb : coefficients g ∈ Function.support P := by
      by_contra hn
      have hz : cut (coefficients g) = 0 := (LocallyConstant.charFn_eq_zero ℂ _ hS).2 hn
      exact hg (show f₀ g = 0 by simp only [f₀, hz, zero_mul])
    obtain ⟨a, ha⟩ := hP hb
    exact ((corresponds_iff_coefficients_eq F D a.property).2 ha.symm).1
  have hcut (b : Fin d → F) : cut b * P b = P b := by
    by_cases hb : P b = 0
    · rw [hb, mul_zero]
    · have hcb : cut b = 1 := (LocallyConstant.charFn_eq_one ℂ _ hS).2 hb
      rw [hcb, one_mul]
  have hfval (g : RF) : orbitalIntegral (g : G) (mF.quotient g) f = P (pF g) := by
    have horbit : twistedOrbitFunction (MonoidHom.id G) g.val (f : G → ℂ) = fun q =>
        cut (pF g) * twistedOrbitFunction (MonoidHom.id G) g.val (A : G → ℂ) q := by
      funext q
      induction q using Quotient.inductionOn with
      | h x =>
        change cut (coefficients (x⁻¹ * g.val * x)) * A (x⁻¹ * g.val * x) =
          cut (coefficients g.val) * A (x⁻¹ * g.val * x)
        rw [coefficients_conj]
    change (∫ q, twistedOrbitFunction (MonoidHom.id G) g.val (f : G → ℂ) q ∂mF.quotient g) = _
    rw [horbit, integral_const_mul, ← twistedOrbitalIntegral, hAval, hcut]
  refine ⟨f, hf, vanishesOffElliptic_of_isEllipticSupported hf μ, ?_⟩
  intro γ a ha
  let g : RF := ⟨γ, ha.1.1⟩
  let b : RD := ⟨a, ha.2.1⟩
  have hcoeff : pF g = pD b := (corresponds_iff_coefficients_eq F D b.property).mp ha
  have heq : orbitalIntegral γ (mF.quotient g) f = orbitalIntegral a (mD.quotient b) f' :=
    (hfval g).trans ((congrArg P hcoeff).trans (hPval b))
  intro η _ _ η' _ _ ν ν' hν hν' hassoc
  obtain ⟨e, _, he⟩ := hassoc
  obtain ⟨kF, hkF⟩ := hmF g
  obtain ⟨kD, hkD⟩ := hmD b
  have hcF := isClosed_twistedCentralizer (MonoidHom.id G) continuous_id γ
  have hcD := isClosed_twistedCentralizer (MonoidHom.id Dˣ) continuous_id a
  let : LocallyCompactSpace (glCentralizer γ) := hcF.locallyCompactSpace
  let : LocallyCompactSpace (divisionCentralizer a) := hcD.locallyCompactSpace
  let : SecondCountableTopology (glCentralizer γ) := IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology (divisionCentralizer a) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  let : (mF.centralizer g).IsHaarMeasure := mF.haar g
  let : (mF.centralizer g).IsMulRightInvariant := mF.rightInvariant g
  let : (mF.centralizer g).Regular := hkF.symm ▸ inferInstanceAs kF.haar.Regular
  let : (mD.centralizer b).IsHaarMeasure := mD.haar b
  let : (mD.centralizer b).IsMulRightInvariant := mD.rightInvariant b
  let : (mD.centralizer b).Regular := hkD.symm ▸ inferInstanceAs kD.haar.Regular
  have hmap : Measure.map e (mF.centralizer g) = mD.centralizer b := by
    rw [hkF, hkD]
    exact kF.map_haar kD e
  let c := haarScalarFactor η (mF.centralizer g)
  have hc : 0 < c := haarScalarFactor_pos_of_isHaarMeasure η (mF.centralizer g)
  have hη : η = c • mF.centralizer g := isMulLeftInvariant_eq_smul η (mF.centralizer g)
  have heMeas : Measurable e := e.continuous.measurable
  have hη' : η' = c • mD.centralizer b := by
    rw [← he, hη, Measure.map_smul _ heMeas.aemeasurable, hmap]
  have hscale := (mF.compatible g).eq_smul_of_subgroup_smul hcF hν hη
  have hscale' := (mD.compatible b).eq_smul_of_subgroup_smul hcD hν' hη'
  rw [hscale, hscale', orbitalIntegral, orbitalIntegral, twistedOrbitalIntegral_smul_measure,
    twistedOrbitalIntegral_smul_measure] at heq
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  exact smul_right_injective ℂ hc' heq

end Langlands.JacquetLanglands
