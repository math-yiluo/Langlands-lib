import Langlands.BaseChange.CyclicProductNormCoordinates
import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.BaseChange.OrbitalMeasureExistence
import Langlands.BaseChange.UnitFundamentalLemmaStatement

/-! # Reduction of the unramified cyclic product unit comparison to the field unit -/

noncomputable section

open MeasureTheory Topology

namespace Langlands.BaseChange

open Correspondence JacquetLanglands QuotientIntegration TraceFormula Unramified

universe u v w

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel
attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

local instance {E : Type v} [CommRing E] [TopologicalSpace E] (n : ℕ) :
    MeasurableSpace (GeneralLinear n E) := borel _
local instance {E : Type v} [CommRing E] [TopologicalSpace E] (n : ℕ) :
    BorelSpace (GeneralLinear n E) := ⟨rfl⟩

/-- The field unit lemma gives concordance of the product unit in an unramified
cyclic algebra supplied with its topological field-product coordinates. -/
def CyclicProductUnitReductionStatement : Prop :=
  UnitFundamentalLemmaStatement.{u, w} →
    ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (L : PadicField.{w} p)
      [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
      (E : Type v) [CommRing E] [Algebra F.Carrier E]
      [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F.Carrier E]
      (σ : E ≃ₐ[F.Carrier] E) (τ : L.Carrier ≃ₐ[F.Carrier] L.Carrier)
      (m d r : ℕ), IsCyclicAlgebra σ ((m + 1) * d) → IsCyclicAlgebra τ d →
      L.canonicalTopologicalData.ramificationIndex = F.canonicalTopologicalData.ramificationIndex →
      ∀ (c : E ≃ₐ[F.Carrier] (Fin (m + 1) → L.Carrier))
        (hc : Continuous c) (hc' : Continuous c.symm),
        (∀ (x : E) (i : Fin m), c (σ x) i.castSucc = c x i.succ) →
        (∀ x : E, c (σ x) (Fin.last m) = τ (c x 0)) →
        let κ := cyclicProductGLCoordinates (n := r + 1) c hc hc'
        AreConcordant σ ((m + 1) * d) (sphericalHaar F r)
          (Measure.map κ.symm (Measure.pi fun _ : Fin (m + 1) ↦ sphericalHaar L r))
          (fun x ↦ (Set.pi Set.univ (fun _ : Fin (m + 1) ↦
            (sphericalSubgroup L r : Set (GeneralLinear (r + 1) L.Carrier)))).indicator
              (fun _ ↦ 1) (κ x))
          ⇑(1 : SphericalHeckeAlgebra F r)

theorem cyclicProductUnitReduction : CyclicProductUnitReductionStatement := by
  intro hunit p _ F L _ _ E _ _ _ _ _ σ τ m d r hcyclic hfield he c hc hc' hshift hwrap
  let n := r + 1
  let G := GeneralLinear n L.Carrier
  let H := GeneralLinear n E
  let κ := cyclicProductGLCoordinates (n := n) c hc hc'
  let μ := sphericalHaar L r
  let μH : Measure H := Measure.map κ.symm (Measure.pi fun _ : Fin (m + 1) ↦ μ)
  let ρ : Measure (Fin (m + 1) → G) := Measure.pi fun _ ↦ μ
  let σG := (entrywiseAut σ n).toMonoidHom
  let τG := (entrywiseAut τ n).toMonoidHom
  have hshiftG (x : H) (i : Fin m) : κ (σG x) i.castSucc = κ x i.succ :=
    cyclicProductGLCoordinates_shift c hc hc' hshift x i
  have hwrapG (x : H) : κ (σG x) (Fin.last m) = τG (κ x 0) :=
    cyclicProductGLCoordinates_wrap c hc hc' hwrap x
  have hunitL := hunit p F L τ d r hfield he
  refine ⟨?_, ?_⟩
  · intro γ hreg hnot
    exact hunitL.1 γ hreg (fun hn ↦ hnot
      ((cyclicProductGLCoordinates_isNorm_iff c hc hc' hshift hwrap d hcyclic.pow_eq_one γ).mpr hn))
  intro δ γ hassoc hreg μδ _ _ μγ _ _ νδ νγ hνδ hνγ hmeas
  let y := (List.ofFn (κ δ)).prod
  let C := sigmaCentralizer σ n δ
  let Z := sigmaCentralizer τ n y
  let e : C ≃ₜ* Z := cyclicProductCentralizerEquiv κ σG τG hshiftG hwrapG δ
  let μZ : Measure Z := Measure.map e μδ
  let : μZ.IsHaarMeasure := e.isHaarMeasure_map μδ
  let : μZ.IsMulRightInvariant := isMulRightInvariant_map e μδ
  have heZ : MeasurePreserving e μδ μZ := ⟨e.continuous.measurable, rfl⟩
  let : IsModuleTopology (Padic p) L.Carrier := L.canonicalTopologicalData.moduleTopology
  have hτG : Continuous τG :=
    (IsModuleTopology.continuous_of_linearMap (τ.toLinearMap.restrictScalars (Padic p))).generalLinearGroup_map
  have hσG : Continuous σG := continuous_entrywiseAut σ n
  let : LocallyCompactSpace G := LocalFieldTopology.generalLinear_locallyCompactSpace L.Carrier n
  let : SecondCountableTopology G := LocalFieldTopology.generalLinear_secondCountableTopology L.Carrier n
  let : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  let : μ.InnerRegular := inferInstance
  let : μ.IsMulRightInvariant := generalLinear_haar_rightInvariant L.Carrier n μ
  have hclosed : IsClosed (Z : Set G) :=
    isClosed_eq ((continuous_inv.mul continuous_const).mul hτG) continuous_const
  let : LocallyCompactSpace Z := hclosed.locallyCompactSpace
  let : TopologicalSpace.PseudoMetrizableSpace G := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace Z :=
    hclosed.isClosedEmbedding_subtypeVal.isEmbedding.isInducing.pseudoMetrizableSpace
  let : μZ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μZ
  obtain ⟨νZ, hνZ⟩ := compatibleMeasureExists Z hclosed μ μZ
  have hassocZ : IsAssociatedMeasure τ d y γ μZ μγ := by
    obtain ⟨a, ha, hm⟩ := hmeas
    let b := κ a 0
    refine ⟨b, ?_, ?_⟩
    · have h := congrArg (fun z : H ↦ κ z 0) ha
      change κ (a⁻¹ * cyclicNorm σ ((m + 1) * d) δ * a) 0 =
        κ (baseChange F.Carrier E n γ) 0 at h
      rw [map_mul, map_mul, map_inv, Pi.mul_apply, Pi.mul_apply, Pi.inv_apply,
        cyclicProductGLCoordinates_norm_zero c hc hc' hshift hwrap,
        cyclicProductGLCoordinates_baseChange c hc hc' γ 0] at h
      exact h
    · have hproj : Measurable (fun z : H ↦ κ z 0) :=
        ((continuous_apply 0).comp κ.continuous).measurable
      have hbase : Continuous (baseChange F.Carrier E n) :=
        (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F.Carrier E)).generalLinearGroup_map
      have hbase' : Measurable (fun t : glCentralizer γ ↦ baseChange F.Carrier E n t.val) :=
        (hbase.comp continuous_subtype_val).measurable
      have hmap := congrArg (Measure.map (fun z : H ↦ κ z 0)) hm
      rw [Measure.map_map hproj (by fun_prop), Measure.map_map hproj hbase'] at hmap
      change Measure.map (fun z : Z ↦ b⁻¹ * z.val * b) (Measure.map e μδ) =
        Measure.map (fun t : glCentralizer γ ↦ baseChange F.Carrier L.Carrier n t.val) μγ
      have hconj : Measurable (fun z : Z ↦ b⁻¹ * z.val * b) := by fun_prop
      have heMeas : Measurable (e : C → Z) := e.continuous.measurable
      rw [Measure.map_map hconj heMeas]
      change Measure.map (fun x : C ↦ b⁻¹ * κ x.val 0 * b) μδ =
        Measure.map (fun t : glCentralizer γ ↦ baseChange F.Carrier L.Carrier n t.val) μγ
      simpa only [Function.comp_def, b, map_mul, map_inv, Pi.mul_apply, Pi.inv_apply,
        κ, cyclicProductGLCoordinates_baseChange] using hmap
  have hκ : MeasurePreserving κ μH ρ := by
    have hforward : Measurable (κ : H → Fin (m + 1) → G) := κ.continuous.measurable
    have hback : Measurable (κ.symm : (Fin (m + 1) → G) → H) := κ.symm.continuous.measurable
    refine ⟨hforward, ?_⟩
    change Measure.map κ (Measure.map κ.symm ρ) = ρ
    rw [Measure.map_map hforward hback]
    simp [Function.comp_def]
  have hK : MeasurableSet (sphericalSubgroup L r : Set G) :=
    (sphericalOpenSubgroup L r).isOpen.measurableSet
  have htransfer :=
    @cyclicProductUnitOrbitalIntegral_eq H _ _ G _ _ _ m κ σG τG hshiftG hwrapG
      _ _ _ _ _ _ _ _ δ hσG hτG μ _ μH hκ μδ
      (inferInstanceAs μδ.IsHaarMeasure) (inferInstanceAs μδ.IsMulRightInvariant)
      μZ (inferInstanceAs μZ.IsHaarMeasure) (inferInstanceAs μZ.IsMulRightInvariant)
      νδ νZ hνδ hνZ heZ (sphericalSubgroup L r) hK (sphericalHaar_self L r)
  have hvalue : (fun x : G ↦ (1 : SphericalHeckeAlgebra L r) x) =
      (sphericalSubgroup L r : Set G).indicator (fun _ ↦ 1) := by
    funext x
    rw [Hecke.HeckeAlgebra.Corner.one_apply, sphericalHaar_real_self]
    change ((1 : ℝ) : ℂ)⁻¹ * (sphericalSubgroup L r : Set G).indicator (fun _ ↦ 1) x = _
    simp
  have hassoc' := (cyclicProductGLCoordinates_normAssociated_iff c hc hc' hshift hwrap d
    hcyclic.pow_eq_one δ γ).mp hassoc
  exact htransfer.trans (by
    rw [← hvalue]
    exact hunitL.2 y γ hassoc' hreg μZ μγ νZ νγ hνZ hνγ hassocZ)

end Langlands.BaseChange
