import Langlands.BaseChange.UnitFundamentalLemmaStatement
import Langlands.BaseChange.SphericalOrbitalCosets
import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.BaseChange.CyclicNormFieldConjugacy
import Langlands.BaseChange.RegularTransferMeasures

/-! The unit fundamental lemma for unramified cyclic base change of `GL_n`. -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory _root_.Topology Correspondence Langlands.JacquetLanglands Langlands.Unramified
open Langlands.QuotientIntegration Langlands.TraceFormula
open scoped ENNReal

universe u v w

variable {p : ℕ} [Fact p.Prime]

local instance unitFieldTopology (L : PadicField.{w} p) : TopologicalSpace L.Carrier :=
  L.canonicalTopologicalData.topology
local instance unitFieldValuativeRel (L : PadicField.{w} p) : ValuativeRel L.Carrier :=
  L.canonicalTopologicalData.valuativeRel
local instance unitFieldLocalField (L : PadicField.{w} p) : IsNonarchimedeanLocalField L.Carrier :=
  L.canonicalTopologicalData.localField
local instance glTopology (L : PadicField.{w} p) (n : ℕ) : TopologicalSpace (GeneralLinear n L.Carrier) :=
  L.canonicalGeneralLinearTopology n
local instance glTopologicalGroup (L : PadicField.{w} p) (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n L.Carrier) := L.canonicalGeneralLinearTopologicalGroup n
local instance glT2 (L : PadicField.{w} p) (n : ℕ) : T2Space (GeneralLinear n L.Carrier) :=
  L.canonicalGeneralLinearT2Space n
local instance glLocallyCompact (L : PadicField.{w} p) (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n L.Carrier) := L.canonicalGeneralLinearLocallyCompactSpace n
local instance glSecondCountable (L : PadicField.{w} p) (n : ℕ) :
    SecondCountableTopology (GeneralLinear n L.Carrier) :=
  LocalFieldTopology.generalLinear_secondCountableTopology L.Carrier n
local instance glMeasurable (L : PadicField.{w} p) (n : ℕ) : MeasurableSpace (GeneralLinear n L.Carrier) :=
  borel _
local instance glBorel (L : PadicField.{w} p) (n : ℕ) : BorelSpace (GeneralLinear n L.Carrier) := ⟨rfl⟩

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

private theorem sphericalUnit_indicator (L : PadicField.{w} p) (r : ℕ) :
    ⇑(1 : SphericalHeckeAlgebra L r) =
      (sphericalOpenSubgroup L r : Set (GeneralLinear (r + 1) L.Carrier)).indicator
        (fun _ => (1 : ℂ)) := by
  funext g
  rw [← standardHeckeElement_zero L r, standardHeckeElement_apply, standardDiagonal_zero,
    Hecke.TestFunction.doubleCosetSet_one]

variable (F : PadicField.{u} p) (E : PadicField.{v} p)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
variable {σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier} {l r : ℕ}
variable {δ : GeneralLinear (r + 1) E.Carrier} {γ : GeneralLinear (r + 1) F.Carrier}

local notation "GF" => GeneralLinear (r + 1) F.Carrier
local notation "GE" => GeneralLinear (r + 1) E.Carrier
local notation "B" => baseChange F.Carrier E.Carrier (r + 1)
local notation "θ" => entrywiseAut σ (r + 1)
local notation "KF" => sphericalOpenSubgroup F r
local notation "KE" => sphericalOpenSubgroup E r
local notation "HF" => glCentralizer γ
local notation "HE" => sigmaCentralizer σ (r + 1) δ
local notation "OF" => compactOpenTwistedDoubleCosets (MonoidHom.id GF) γ KF
local notation "OE" => compactOpenTwistedDoubleCosets θ δ KE

private theorem sphericalConjugate_baseChange (y : GF) (hy : y⁻¹ * γ * y ∈ KF) :
    (B y)⁻¹ * B γ * B y ∈ KE := by
  change (B y)⁻¹ * B γ * B y ∈ sphericalSubgroup E r
  simpa only [map_mul, map_inv] using
    (baseChange_mem_sphericalSubgroup_iff F E (y⁻¹ * γ * y)).mpr hy

private theorem sphericalStabilizer_measure_eq (s : GE) (y : GF)
    (μδ : Measure HE) (μγ : Measure HF)
    (hm : Measure.map (fun c : HE => s⁻¹ * c.val * s) μδ =
      Measure.map (fun t : HF => B t.val) μγ) :
    μδ {c : HE | (s * B y)⁻¹ * c.val * (s * B y) ∈ KE} =
      μγ {t : HF | y⁻¹ * t.val * y ∈ KF} := by
  let := canonicalRelativeModuleTopology F E
  have hb : Continuous B :=
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F.Carrier E.Carrier)).generalLinearGroup_map
  have hc : Continuous (fun c : HE => s⁻¹ * c.val * s) :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  have ht : Continuous (fun t : HF => B t.val) := hb.comp continuous_subtype_val
  let U : Set GE := {g | (B y)⁻¹ * g * B y ∈ KE}
  have hU : MeasurableSet U :=
    ((KE).isOpen.preimage ((continuous_const.mul continuous_id).mul continuous_const)).measurableSet
  have h := congrArg (fun μ : Measure GE => μ U) hm
  change Measure.map _ _ U = Measure.map _ _ U at h
  rw [Measure.map_apply hc.measurable hU, Measure.map_apply ht.measurable hU] at h
  have he : (fun c : HE => s⁻¹ * c.val * s) ⁻¹' U =
      {c : HE | (s * B y)⁻¹ * c.val * (s * B y) ∈ KE} := by
    ext c
    change (B y)⁻¹ * (s⁻¹ * c.val * s) * B y ∈ KE ↔ (s * B y)⁻¹ * c.val * (s * B y) ∈ KE
    rw [show (B y)⁻¹ * (s⁻¹ * c.val * s) * B y = (s * B y)⁻¹ * c.val * (s * B y) by group]
  have hf : (fun t : HF => B t.val) ⁻¹' U = {t : HF | y⁻¹ * t.val * y ∈ KF} := by
    ext t
    change (B y)⁻¹ * B t.val * B y ∈ sphericalSubgroup E r ↔ y⁻¹ * t.val * y ∈ sphericalSubgroup F r
    rw [← map_inv, ← map_mul, ← map_mul, baseChange_mem_sphericalSubgroup_iff F E]
  rwa [he, hf] at h

private theorem sphericalUnit_vanishesOffNorms (hσ : IsCyclicAlgebra σ l)
    (he : E.canonicalTopologicalData.ramificationIndex = F.canonicalTopologicalData.ramificationIndex) :
    VanishesOffNorms σ l (sphericalHaar F r) ⇑(1 : SphericalHeckeAlgebra F r) := by
  intro γ _ hNotNorm μγ _ _ νγ _
  let : IsEmpty (compactOpenTwistedDoubleCosets (MonoidHom.id GF) γ KF) := ⟨fun d => by
    obtain ⟨u, hu, _⟩ := exists_spherical_cyclicNorm_lift F E hσ he γ
      ⟨B d.val.out, sphericalConjugate_baseChange F E d.val.out d.property⟩
    exact hNotNorm ⟨u, 1, by simpa only [inv_one, one_mul, mul_one] using hu⟩⟩
  change twistedOrbitalIntegral (MonoidHom.id GF) γ νγ ⇑(1 : SphericalHeckeAlgebra F r) = 0
  rw [sphericalUnit_indicator, twistedOrbitalIntegral_compactOpen _ _ _ (fun _ h => h)]
  simp

private theorem sphericalUnit_concordAt (hσ : IsCyclicAlgebra σ l)
    (he : E.canonicalTopologicalData.ramificationIndex = F.canonicalTopologicalData.ramificationIndex)
    (hγ : IsRegularSemisimple γ) :
    ConcordAt σ l (sphericalHaar F r) (sphericalHaar E r)
      ⇑(1 : SphericalHeckeAlgebra E r) ⇑(1 : SphericalHeckeAlgebra F r) δ γ := by
  classical
  intro μδ _ _ μγ _ _ νδ νγ hνδ hνγ hm
  obtain ⟨x, hx, hpush⟩ := hm
  have hθK : ∀ k ∈ KE, θ k ∈ KE := fun _ hk => entrywiseAut_mem_sphericalSubgroup F E σ hk
  change twistedOrbitalIntegral θ δ νδ ⇑(1 : SphericalHeckeAlgebra E r) =
    twistedOrbitalIntegral (MonoidHom.id GF) γ νγ ⇑(1 : SphericalHeckeAlgebra F r)
  rw [sphericalUnit_indicator E r, sphericalUnit_indicator F r,
    twistedOrbitalIntegral_compactOpen θ δ KE hθK,
    twistedOrbitalIntegral_compactOpen (MonoidHom.id GF) γ KF (fun _ h => h)]
  by_cases hint : ∃ z : GE, z⁻¹ * B γ * z ∈ sphericalSubgroup E r
  · obtain ⟨u, hu, huInt⟩ := exists_spherical_cyclicNorm_lift F E hσ he γ hint
    obtain ⟨s, hs⟩ := twistedConj_of_cyclicNorm_conj_of_field hσ x (hx.trans hu.symm)
    have hsN : s⁻¹ * cyclicNorm σ l δ * s = B γ := by
      have h := congrArg (cyclicNorm σ l) hs
      rwa [cyclicNorm_twistedConj, hσ.pow_eq_one, entrywiseAut_one_apply, hu] at h
    let := hσ.1
    have hcs : (fun c : HE => x⁻¹ * c.val * x) = fun c : HE => s⁻¹ * c.val * s :=
      funext (normConjugator_on_sigmaCentralizer hσ.pow_eq_one
        (fun _ _ ha hb => commute_of_commute_baseChange hγ ha hb) hx hsN)
    rw [hcs] at hpush
    let e := sphericalOrbitalCosetsEquiv F E hσ he hγ s u hs hsN hu huInt
    let := canonicalRelativeModuleTopology F E
    have hclosedF : IsClosed (HF : Set GF) :=
      isClosed_twistedCentralizer (MonoidHom.id GF) continuous_id γ
    have hclosedE : IsClosed (HE : Set GE) :=
      isClosed_twistedCentralizer θ (continuous_entrywiseAut σ (r + 1)) δ
    let : LocallyCompactSpace HF := hclosedF.locallyCompactSpace
    let : LocallyCompactSpace HE := hclosedE.locallyCompactSpace
    let : SecondCountableTopology HF := IsEmbedding.subtypeVal.secondCountableTopology
    let : SecondCountableTopology HE := IsEmbedding.subtypeVal.secondCountableTopology
    let : μγ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
    let : μδ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
    let : (sphericalHaar F r).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
    let : (sphericalHaar E r).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
    have hmass (d : OF) : νδ (compactOpenDoubleCoset HE KE (e d).val) =
        νγ (compactOpenDoubleCoset HF KF d.val) := by
      let y := d.val.out
      have hdE : (e d).val = DoubleCoset.mk HE (KE).toSubgroup (s * B y) :=
        sphericalOrbitalCosetsEquiv_apply_val F E hσ he hγ s u hs hsN hu huInt d
      have hdF : DoubleCoset.mk HF (KF).toSubgroup y = d.val := DoubleCoset.out_eq' _
      calc
        _ = νδ (compactOpenDoubleCoset HE KE (DoubleCoset.mk HE (KE).toSubgroup (s * B y))) := by rw [hdE]
        _ = 1 / μδ {c : HE | (s * B y)⁻¹ * c.val * (s * B y) ∈ KE} := by
          simpa only [sphericalHaar_self] using IsCompatible.measure_compactOpenDoubleCoset
            HE (sphericalHaar E r) μδ hclosedE KE (sphericalOpenSubgroup_isCompact E r) νδ hνδ (s * B y)
        _ = 1 / μγ {t : HF | y⁻¹ * t.val * y ∈ KF} := by
          rw [sphericalStabilizer_measure_eq F E s y μδ μγ hpush]
        _ = νγ (compactOpenDoubleCoset HF KF (DoubleCoset.mk HF (KF).toSubgroup y)) := by
          symm
          simpa only [sphericalHaar_self] using IsCompatible.measure_compactOpenDoubleCoset
            HF (sphericalHaar F r) μγ hclosedF KF (sphericalOpenSubgroup_isCompact F r) νγ hνγ y
        _ = _ := by rw [hdF]
    exact congrArg (fun m : ℝ≥0∞ => (m.toReal : ℂ))
      ((e.tsum_eq (fun d : OE => νδ (compactOpenDoubleCoset HE KE d.val))).symm.trans (tsum_congr hmass))
  · let : IsEmpty OF := ⟨fun d => hint
      ⟨B d.val.out, sphericalConjugate_baseChange F E d.val.out d.property⟩⟩
    let : IsEmpty OE := ⟨fun d => by
      apply hint
      let y := d.val.out
      have hy : y⁻¹ * δ * θ y ∈ sphericalSubgroup E r := d.property
      have hn := cyclicNorm_mem_sphericalSubgroup F E σ l hy
      rw [cyclicNorm_twistedConj, hσ.pow_eq_one, entrywiseAut_one_apply] at hn
      refine ⟨x⁻¹ * y, ?_⟩
      rw [← hx, show (x⁻¹ * y)⁻¹ * (x⁻¹ * cyclicNorm σ l δ * x) * (x⁻¹ * y) =
        y⁻¹ * cyclicNorm σ l δ * y by group]
      exact hn⟩
    simp

/-- The unit elements of the spherical Hecke algebras concord under unramified
cyclic base change, with the associated measures of the Library statement. -/
theorem unitFundamentalLemma : UnitFundamentalLemmaStatement.{u, v} := by
  intro p _ F E _ _ σ l r hσ he
  refine ⟨sphericalUnit_vanishesOffNorms F E hσ he, ?_⟩
  intro δ γ _ hγ
  exact sphericalUnit_concordAt F E hσ he hγ

end Langlands.BaseChange
