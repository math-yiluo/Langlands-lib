import Langlands.Analysis.Local.WeylChartTranslate
import Langlands.BaseChange.OrdinaryWeylHaarLocalPushforwardsStatement
import Langlands.BaseChange.OrdinaryWeylDifferential
import Langlands.BaseChange.WeylHaarScaling
import Langlands.BaseChange.FiniteAlgebraAnalyticNorm
import Langlands.BaseChange.RegularSetOpenConull
import Langlands.BaseChange.GeneralLinearFiniteAlgebra

/-! # Ordinary local Haar pushforwards for Weyl integration -/

open MeasureTheory Measure Set Topology
open scoped NNReal ENNReal

namespace Langlands.BaseChange

open Langlands.JacquetLanglands Langlands.QuotientIntegration Langlands.Analysis.WeylChart

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u

namespace WeylTorus

variable {F : Type u} [Field F] {n : ℕ}

/-- The rational points of a maximal torus commute with each other. -/
theorem val_mul_comm (T : WeylTorus F n) (a b : T.val) : a * b = b * a := by
  obtain ⟨γ, hγ, hT⟩ := T.property
  have ha : a.val ∈ glCentralizer γ := by rw [hT]; exact a.property
  have hb : b.val ∈ glCentralizer γ := by rw [hT]; exact b.property
  have h := congrArg Subtype.val (glCentralizer_mul_comm hγ ⟨a.val, ha⟩ ⟨b.val, hb⟩)
  exact Subtype.ext h

/-- At a regular point the Weyl discriminant is nonzero. -/
theorem weylDiscriminant_ne_zero (T : WeylTorus F n) (t : T.regularPoints) :
    weylDiscriminant t.val.val ≠ 0 := by
  obtain ⟨hu, he⟩ := det_ordinaryWeylDifferential t.val.val t.property
  rw [← he]
  exact hu.ne_zero

end WeylTorus

theorem ordinaryWeylHaarLocalPushforwards : OrdinaryWeylHaarLocalPushforwardsStatement.{u} := by
  intro F _ _ _ _ n _ _ μ _ T μT _ _ ν hν
  rintro ⟨q₀, t₀⟩
  classical
  -- the analytic structures on `F` and on the matrix algebra
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : CompleteSpace F := LocalGalois.localNormedField_complete F
  let : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
  let : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : IsModuleTopology F (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (IsModuleTopology F (Fin n → Fin n → F))
  let : NormedRing (Matrix (Fin n) (Fin n) F) := finiteAlgebraNormedRing F _
  let : NormedAlgebra F (Matrix (Fin n) (Fin n) F) := finiteAlgebraNormedAlgebra F _
  let : ProperSpace (Matrix (Fin n) (Fin n) F) := FiniteDimensional.proper F _
  let : @CompleteSpace (Matrix (Fin n) (Fin n) F) PseudoMetricSpace.toUniformSpace :=
    complete_of_proper
  let : IsUltrametricDist (Matrix (Fin n) (Fin n) F) := finiteAlgebraNormedRing_ultrametric F _
  let : MeasurableSpace (Matrix (Fin n) (Fin n) F) := borel _
  let : BorelSpace (Matrix (Fin n) (Fin n) F) := ⟨rfl⟩
  -- topology and invariance on the groups
  have : T2Space (GeneralLinear n F) := LocalFieldTopology.generalLinear_t2Space F n
  have : SecondCountableTopology (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_secondCountableTopology F n
  have : LocallyCompactSpace (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have : μ.IsMulRightInvariant := generalLinear_haar_rightInvariant F n μ
  set γ : GeneralLinear n F := t₀.val.val with hγdef
  have hreg : IsRegularSemisimple γ := t₀.property
  have hTγ : glCentralizer γ = T.val := T.glCentralizer_eq_of_regularPoint t₀
  have hTclosed : IsClosed (T.val : Set (GeneralLinear n F)) := by
    have hset : (T.val : Set (GeneralLinear n F)) = {u | u * γ = γ * u} := by
      ext u
      rw [← hTγ, glCentralizer_eq_centralizer]
      exact Subgroup.mem_centralizer_singleton_iff
    rw [hset]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have : LocallyCompactSpace T.val := hTclosed.locallyCompactSpace
  have : SecondCountableTopology T.val := IsInducing.subtypeVal.secondCountableTopology
  have : SecondCountableTopology T.regularPoints := IsInducing.subtypeVal.secondCountableTopology
  have : LocallyCompactSpace (LeftQuotient T.val) := leftQuotient_locallyCompactSpace T.val
  have : SecondCountableTopology (LeftQuotient T.val) :=
    _root_.Topology.IsOpenQuotientMap.secondCountableTopology
      (leftQuotient_isOpenQuotientMap T.val)
  -- the regular position of `γ` and the identification of the torus
  have hdef : defect F γ = adjointDefect γ := by
    apply LinearMap.ext
    intro X
    rw [defect_apply, adjointDefect_apply]
  have hcompl : IsCompl (LinearMap.ker (defect F γ)) (LinearMap.range (defect F γ)) := by
    rw [hdef]
    exact isCompl_ker_range_adjointDefect γ hreg
  have hγ : IsRegularPosition F γ := isRegularPosition_of_isCompl hcompl
  have hH : T.val = torusGroup γ := hTγ.symm.trans (glCentralizer_eq_centralizer γ)
  -- the chart scale is the inverse absolute discriminant
  have hscale : chartScale hγ = (residueAbsoluteNNReal F (weylDiscriminant γ))⁻¹ := by
    apply chartScale_eq_of_map
    have hdet : (chartDifferential hγ).toLinearEquiv.toLinearMap.det = weylDiscriminant γ := by
      rw [chartDifferential_eq hγ hcompl]
      have key : ∀ (d : Matrix (Fin n) (Fin n) F →ₗ[F] Matrix (Fin n) (Fin n) F)
          (h : IsCompl (LinearMap.ker d) (LinearMap.range d)), d = adjointDefect γ →
          ((LinearMap.ker d).projection (LinearMap.range d) h - d).det = weylDiscriminant γ := by
        rintro d h rfl
        exact (det_ordinaryWeylDifferential γ hreg).2
      exact key _ hcompl hdef
    have h := map_linearEquiv_residueAbsolute F (ringHaar hγ) (chartDifferential hγ)
    rw [hdet] at h
    exact h
  have hD : weylDiscriminant γ ≠ 0 := T.weylDiscriminant_ne_zero t₀
  set w₀ := T.discriminantWeight t₀ with hw₀def
  have hw₀ : w₀ = residueAbsoluteNNReal F (weylDiscriminant γ) := rfl
  have hw : (w₀ : ℝ≥0∞) * (chartScale hγ : ℝ≥0∞) = 1 := by
    have hne : residueAbsoluteNNReal F (weylDiscriminant γ) ≠ 0 :=
      hw₀ ▸ (T.discriminantWeight_pos t₀ hD).ne'
    rw [hscale, hw₀, ← ENNReal.coe_mul, mul_inv_cancel₀ hne, ENNReal.coe_one]
  -- a neighbourhood on which the weight is constant
  have hregOpen : IsOpen T.regularPoints :=
    (regularSemisimpleOpenConull F n).1.preimage continuous_subtype_val
  set U₀ : Set T.regularPoints := T.discriminantWeight ⁻¹' {w₀}
  have hU₀ : IsOpen U₀ :=
    (T.isLocallyConstant_discriminantWeight (T.weylDiscriminant_ne_zero)).isOpen_fiber w₀
  obtain ⟨g₀, rfl⟩ : ∃ g₀, leftQuotientMap T.val g₀ = q₀ := Quotient.exists_rep q₀
  set N : Set (LeftQuotient T.val × T.val) := univ ×ˢ (Subtype.val '' U₀)
  have hN : N ∈ 𝓝 (leftQuotientMap T.val g₀, t₀.val) :=
    (isOpen_univ.prod (hregOpen.isOpenEmbedding_subtypeVal.isOpenMap _ hU₀)).mem_nhds
      ⟨trivial, t₀, rfl, rfl⟩
  obtain ⟨W, hWN, hWo, hW0, hWemb, hWmap⟩ :=
    exists_orbitMap_localPushforward_of_eq hγ hH T.val_mul_comm μ μT ν hν g₀ t₀.val rfl hN
  -- pass to the regular points
  let ι : LeftQuotient T.val × T.regularPoints → LeftQuotient T.val × T.val :=
    Prod.map id Subtype.val
  have hι : IsOpenEmbedding ι := IsOpenEmbedding.id.prodMap hregOpen.isOpenEmbedding_subtypeVal
  have hWsub : W ⊆ range ι := by
    intro z hz
    obtain ⟨-, t, -, htz⟩ := hWN hz
    exact ⟨(z.1, t), Prod.ext rfl htz⟩
  have horbit : T.ordinaryOrbitMap = orbitMap T.val_mul_comm ∘ ι := by
    funext p
    obtain ⟨q, t⟩ := p
    induction q using Quotient.inductionOn with
    | h x => rfl
  refine ⟨ι ⁻¹' W, hW0, hWo.preimage hι.continuous, ?_, ?_⟩
  · have heq : (fun z : (ι ⁻¹' W) => T.ordinaryOrbitMap z.val) =
        (fun z : W => orbitMap T.val_mul_comm z.val) ∘ W.restrictPreimage ι := by
      funext z
      rw [horbit]
      rfl
    rw [heq]
    exact hWemb.comp (hι.restrictPreimage W)
  · have hVm : MeasurableSet (ι ⁻¹' W) := (hWo.preimage hι.continuous).measurableSet
    have hWm : MeasurableSet W := hWo.measurableSet
    have := hν.regular
    set ρ₀ := ν.prod (μT.comap Subtype.val)
    -- the weight is constant on the patch
    have hweight :
        (T.weightedOrdinaryOrbitMeasure ν (μT.comap Subtype.val) T.discriminantWeight).restrict
          (ι ⁻¹' W) = (w₀ : ℝ≥0∞) • ρ₀.restrict (ι ⁻¹' W) := by
      rw [WeylTorus.weightedOrdinaryOrbitMeasure, restrict_withDensity hVm, ← withDensity_const]
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem hVm] with z hz
      obtain ⟨-, t, ht, htz⟩ := hWN hz
      have hzt : z.2 = t := Subtype.ext htz.symm
      rw [hzt]
      exact congrArg _ (Set.mem_singleton_iff.mp ht)
    -- the torus measure restricted to the regular points
    have hSm : MeasurableSet T.regularPoints := hregOpen.measurableSet
    have hval : MeasurableEmbedding (Subtype.val : T.regularPoints → T.val) :=
      MeasurableEmbedding.subtype_coe hSm
    have hcomap : (μT.comap Subtype.val).map (Subtype.val : T.regularPoints → T.val) =
        μT.restrict T.regularPoints := by
      rw [hval.map_comap, Subtype.range_coe]
    have : SigmaFinite (μT.comap (Subtype.val : T.regularPoints → T.val)) :=
      SigmaFinite.of_map _ hval.measurable.aemeasurable (by rw [hcomap]; infer_instance)
    have hρ₀ : ρ₀.map ι = (ν.prod μT).restrict (univ ×ˢ T.regularPoints) := by
      rw [← Measure.map_prod_map ν _ measurable_id hval.measurable, Measure.map_id, hcomap,
        ← Measure.prod_restrict, Measure.restrict_univ]
    have hmapι : (ρ₀.restrict (ι ⁻¹' W)).map ι = (ν.prod μT).restrict W := by
      rw [← hι.measurableEmbedding.restrict_map, hρ₀, Measure.restrict_restrict hWm]
      congr 1
      apply inter_eq_left.mpr
      intro z hz
      obtain ⟨-, t, -, htz⟩ := hWN hz
      exact ⟨trivial, htz ▸ t.property⟩
    have hcmeas : Measurable (orbitMap T.val_mul_comm) := (continuous_orbitMap _).measurable
    have himage : T.ordinaryOrbitMap '' (ι ⁻¹' W) = orbitMap T.val_mul_comm '' W := by
      rw [horbit, image_comp, image_preimage_eq_of_subset hWsub]
    rw [hweight, himage, horbit, Measure.map_smul,
      ← Measure.map_map hcmeas hι.continuous.measurable, hmapι, hWmap, smul_smul, hw, one_smul]
    exact (hcmeas.comp hι.continuous.measurable).aemeasurable
