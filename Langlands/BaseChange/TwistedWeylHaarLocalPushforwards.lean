import Langlands.Analysis.Local.AffineQuotientHaar
import Langlands.Analysis.Local.AffineUnitBalls
import Langlands.BaseChange.TwistedOrbitAffineChart
import Langlands.BaseChange.TwistedWeylDifferential
import Langlands.BaseChange.TwistedWeylHaarLocalPushforwardsStatement
import Langlands.BaseChange.WeylHaarScaling
import Langlands.BaseChange.WeylTorusHaarCharts
import Langlands.BaseChange.WeylTorusNormDifferential

/-! # Twisted local Haar pushforwards for Weyl integration on `GL_n` -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.Analysis Langlands.JacquetLanglands Langlands.QuotientIntegration
open Filter MeasureTheory MeasureTheory.Measure Metric Set _root_.Topology
open scoped NNReal

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

set_option maxHeartbeats 1200000 in
/-- Henniart–Lemaire, II.2.10, formula (1), on open branches of the
cyclically twisted Weyl map with the given compatible Haar measures. -/
theorem twistedWeylHaarLocalPushforwards : TwistedWeylHaarLocalPushforwardsStatement.{u, v} := by
  classical
  intro F _ _ _ _ E _ _ _ _ _ σ l n hσ _ _ _ _ μ _ T μT _ H μH _ _ ν hμH hν
  let G := GeneralLinear n E
  let Q := LeftQuotient H
  let A := T.regularNormPoints σ l
  let MF := Matrix (Fin n) (Fin n) F
  let R := Matrix (Fin n) (Fin n) E
  let : Module.Finite F E := hσ.1
  let : Nontrivial E := Module.finrank_pos_iff.mp (hσ.2.1 ▸ hσ.pos)
  let : IsReduced E := hσ.2.2.1
  let : IsArtinianRing E := IsArtinianRing.of_finite F E
  let : T2Space F := LocalFieldTopology.t2Space F
  let : SecondCountableTopology F := LocalFieldTopology.secondCountableTopology F
  let : T2Space (GeneralLinear n F) := LocalFieldTopology.generalLinear_t2Space F n
  let : LocallyCompactSpace (GeneralLinear n F) := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let : SecondCountableTopology (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_secondCountableTopology F n
  let : LocallyCompactSpace T.val := T.isClosed_val.locallyCompactSpace
  let : SecondCountableTopology T.val := IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨hE₂, hEc, hEs⟩ := finiteAlgebraTopology F E
  let : T2Space E := hE₂
  let : LocallyCompactSpace E := hEc
  let : SecondCountableTopology E := hEs
  let : T2Space R := inferInstanceAs (T2Space (Fin n → Fin n → E))
  let : LocallyCompactSpace R := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → E))
  let : SecondCountableTopology R := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → E))
  let : SecondCountableTopology G := generalLinear_secondCountable_of_finiteAlgebra (F := F) n
  let : T2Space G := Units.isEmbedding_embedProduct.t2Space
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace (GeneralLinear n E))
  let : μ.IsMulRightInvariant := generalLinear_haar_rightInvariant E n μ
  have hH : IsClosed (H : Set G) :=
    (hσ.isClosedEmbedding_baseChange n).isClosedMap (T.val : Set (GeneralLinear n F)) T.isClosed_val
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : SecondCountableTopology H := IsEmbedding.subtypeVal.secondCountableTopology
  let : LocallyCompactSpace Q := leftQuotient_locallyCompactSpace H
  let : SecondCountableTopology Q := (leftQuotient_isOpenQuotientMap H).secondCountableTopology
  let : T2Space Q := leftQuotient_t2Space H hH
  let : ν.Regular := hν.regular
  let : SFinite ν := inferInstance
  let eH := T.baseChangeEquiv hσ
  have hHe : Measurable eH := eH.continuous.measurable
  have hμH' : μT.map eH = μH := T.map_baseChangeEquiv eH (T.baseChangeEquiv_val hσ) hH μT μH hμH
  have hAo : IsOpen (A : Set T.val) := T.isOpen_regularNormPoints hσ
  let τ : Measure A := μT.comap Subtype.val
  have hτ : τ.map Subtype.val = μT.restrict (A : Set T.val) :=
    map_comap_subtype_coe hAo.measurableSet μT
  let : SigmaFinite τ := SigmaFinite.of_map τ measurable_subtype_coe.aemeasurable
    (hτ.symm ▸ inferInstanceAs (SigmaFinite (μT.restrict (A : Set T.val))))
  obtain ⟨a, ha, hT⟩ := T.property
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : CompleteSpace F := LocalGalois.localNormedField_complete F
  let : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
  let : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : NormedAddCommGroup (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → F))
  let : NormedSpace F (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (NormedSpace F (Fin n → Fin n → F))
  let : Module.Finite F MF := inferInstanceAs (Module.Finite F (Fin n → Fin n → F))
  let : IsUltrametricDist (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (IsUltrametricDist (Fin n → Fin n → F))
  let : Module.Finite F R := inferInstanceAs (Module.Finite F (Fin n → Fin n → E))
  let : IsModuleTopology F R := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  let : NormedRing R := finiteAlgebraNormedRing F R
  let : NormedAlgebra F R := finiteAlgebraNormedAlgebra F R
  let : CompleteSpace R := FiniteDimensional.complete F R
  let : IsUltrametricDist R := finiteAlgebraNormedRing_ultrametric F R
  let : MeasurableSpace R := borel R
  let : BorelSpace R := ⟨rfl⟩
  obtain ⟨lift, hlift, hlocalLift⟩ := T.exists_normLifts_with_localDifferentials hσ ha hT
  refine ⟨hAo.measurableSet, lift, hlift, ?_⟩
  let S₀ := weylTorusLie a
  let S := ↥S₀
  let i : S →ₗ[F] R := weylTorusLieInclusion a
  have hi : Function.Injective i := matrixBaseChangeLinear_injective.comp Subtype.val_injective
  obtain ⟨W₀, hW₀⟩ := i.range.exists_isCompl
  let W := ↥W₀
  let X := S × W
  let : NormedAddCommGroup S := Submodule.normedAddCommGroup S₀
  let : NormedSpace F S := Submodule.normedSpace S₀
  let : NormedAddCommGroup W := Submodule.normedAddCommGroup W₀
  let : NormedSpace F W := Submodule.normedSpace W₀
  let : ProperSpace S := FiniteDimensional.proper F S
  let : ProperSpace W := FiniteDimensional.proper F W
  let : IsUltrametricDist S := inferInstanceAs (IsUltrametricDist {x : MF // x ∈ S₀})
  let : IsUltrametricDist W := inferInstanceAs (IsUltrametricDist {x : R // x ∈ W₀})
  let : IsUltrametricDist X := ⟨fun x y z => by
    rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
    exact max_le
      ((IsUltrametricDist.dist_triangle_max x.1 y.1 z.1).trans
        (max_le_max (le_max_left _ _) (le_max_left _ _)))
      ((IsUltrametricDist.dist_triangle_max x.2 y.2 z.2).trans
        (max_le_max (le_max_right _ _) (le_max_right _ _)))⟩
  let : SecondCountableTopology MF := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))
  let : SecondCountableTopology S := IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology W := IsEmbedding.subtypeVal.secondCountableTopology
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  let e : X ≃L[F] R := (((LinearEquiv.ofInjective i hi).prodCongr (LinearEquiv.refl F W)).trans
    (Submodule.prodEquivOfIsCompl i.range W₀ hW₀)).toContinuousLinearEquiv
  have he (x : X) : e x = i x.1 + x.2.val := rfl
  let j : W →L[F] R := (e : X →L[F] R).comp (ContinuousLinearMap.inr F S W)
  have hj (x : W) : j x = x.val := by
    change e (0, x) = _
    rw [he]
    simp
  let p : R →ₗ[F] S := (LinearMap.fst F S W).comp e.symm.toLinearEquiv.toLinearMap
  have hei (x : S) : e (x, 0) = i x := by rw [he]; simp
  have hp (x : S) : p (i x) = x := by
    change (e.symm (i x)).1 = x
    rw [← hei, e.symm_apply_apply]
  let ξS : Measure S := addHaar
  let ξW : Measure W := addHaar
  let η := ξS.prod ξW
  let ξ := η.map e
  let : ξ.IsAddHaarMeasure := e.isAddHaarMeasure_map η
  let ε : X ≃L[F] X := (ContinuousLinearEquiv.refl F S).prodCongr (ContinuousLinearEquiv.neg F)
  have hε : η.map ε = η := by
    change η.map (Prod.map id Neg.neg) = η
    rw [← Measure.map_prod_map _ _ measurable_id measurable_neg, Measure.map_id, Measure.map_neg_eq_self]
  let aT := T.affineCoordinate hT
  have haT : IsOpenEmbedding aT := T.isOpenEmbedding_affineCoordinate hT
  let aH : H → S := aT ∘ eH.symm
  have haH : IsOpenEmbedding aH := haT.comp eH.symm.toHomeomorph.isOpenEmbedding
  have haH₀ : aH 1 = 0 := by simp [aH, aT]
  have haHG (x : H) : unitAffine (x.val : G) = e (aH x, 0) := by
    rw [hei]
    have hh := congrArg (fun h : H => h.val.val) (eH.apply_symm_apply x)
    change (algebraMap F E).mapMatrix (eH.symm x).val.val = x.val.val at hh
    change x.val.val - 1 = (algebraMap F E).mapMatrix ((eH.symm x).val.val - 1)
    rw [map_sub, map_one, hh]
  have hiB : IsOpenEmbedding (unitAffine : G → R) := isOpenEmbedding_unitAffine
  obtain ⟨rK, hrK, hKs⟩ := exists_compactOpenSubgroup_affineBall e
  obtain ⟨K₀, hK₀c, hK₀r⟩ := hKs rK hrK le_rfl
  have hK₀ : unitAffine '' (K₀ : Set G) = e '' closedBall 0 rK := by
    rw [← hK₀r, ← Subtype.range_coe (s := (K₀ : Set G)), ← range_comp]
    rfl
  obtain ⟨cG, _, hμ₀⟩ := unitsAffineHaar R Units.isOpenEmbedding_val K₀ hK₀c μ ξ
  have hμG₀ : (μ.restrict (K₀ : Set G)).map unitAffine =
      cG • ξ.restrict (unitAffine '' (K₀ : Set G)) := by
    have hR : range (fun k : K₀ => (k : G).val - 1) = unitAffine '' (K₀ : Set G) := by
      change range (unitAffine ∘ (Subtype.val : K₀ → G)) = _
      rw [range_comp, Subtype.range_coe]
    rw [← hR]
    exact hμ₀
  obtain ⟨rφ, hrφ, hφ⟩ := exists_strictDerivative_ballChart η (affineFactorization e) e
    (hasStrictFDerivAt_affineFactorization e) (affineFactorization_zero e)
  let w (t : A) : ℝ≥0 := T.discriminantWeight ⟨t.val, t.property.1⟩
  let ρ := T.weightedTwistedOrbitMeasure σ l ν τ w
  let orbit := T.twistedOrbitMap hσ lift hlift
  have hw : IsLocallyConstant w := IsLocallyConstant.iff_eventually_eq _ |>.mpr fun t =>
    (continuous_subtype_val.subtype_mk (fun t : A => t.property.1)).continuousAt.eventually
      ((T.isLocallyConstant_discriminantWeight fun y => by
        obtain ⟨hdet, heq⟩ := det_ordinaryWeylDifferential y.val.val y.property
        exact heq ▸ hdet.ne_zero).eventually_eq ⟨t.val, t.property.1⟩)
  rintro ⟨q, t₀⟩
  obtain ⟨g, rfl⟩ := Quotient.exists_rep q
  obtain ⟨f, s, hf₀, hf, hflocal⟩ := hlocalLift t₀
  let δ := (lift t₀).val
  let Aδ := twistedAdjointAlgEquiv σ δ
  let A' := Aδ.toLinearMap.toContinuousLinearMap
  let D : Module.End F R := 1 - Aδ.toLinearMap + s.toLinearMap.comp p
  have hs := T.normLiftDifferential hσ lift hlift (a := a) t₀ f s hf₀ hf hflocal
  obtain ⟨hD, hDet⟩ := T.det_twistedWeylDifferential_of_lie_eq hσ t₀.property.1 (lift t₀)
    (hlift t₀) (T.lie_eq_of_regular ha hT t₀.property.1) p hp s.toLinearMap
    (fun x => (hs x).1) (fun x => (hs x).2)
  change IsUnit D.det at hD
  change D.det = weylDiscriminant t₀.val.val at hDet
  let D' : R ≃L[F] R := (LinearMap.equivOfIsUnitDet hD).toContinuousLinearEquiv
  let e' : X ≃L[F] R := (ε.trans e).trans D'
  have hD' (x : R) : D' x = D x := LinearMap.equivOfIsUnitDet_apply hD x
  have hAi (x : S) : Aδ (i x) = i x := by
    let aT' : T.val := ⟨a, by
      rw [← hT, glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]⟩
    have hc : Commute δ.val (i x) :=
      T.commute_weylTorusLieInclusion hσ (t := aT') ha (lift t₀) x
    change δ.val * matrixEntrywiseAut σ (i x) * (δ⁻¹ : G).val = _
    rw [show matrixEntrywiseAut σ (i x) = i x from matrixEntrywiseAut_baseChange σ x.val,
      hc.eq, mul_assoc, show δ.val * (δ⁻¹ : G).val = (1 : R) from δ.val_inv, mul_one]
  let ψ := twistedOrbitAffineChart A' j f
  have hψd : HasStrictFDerivAt ψ (e' : X →L[F] R) 0 := by
    have hder := hasStrictFDerivAt_twistedOrbitAffineChart A' j hf₀ hf
    have he' (x : X) : e' x = s x.1 + (A' (j x.2) - j x.2) := by
      change D' (e (x.1, -x.2)) = _
      have hsum : e (x.1, -x.2) = i x.1 - j x.2 := by
        rw [he, hj, sub_eq_add_neg]
        rfl
      have hproj : p (e (x.1, -x.2)) = x.1 := by
        change (e.symm (e (x.1, -x.2))).1 = x.1
        rw [e.symm_apply_apply]
      rw [hD']
      change e (x.1, -x.2) - Aδ (e (x.1, -x.2)) + s (p (e (x.1, -x.2))) = _
      rw [hproj, hsum, map_sub, hAi]
      change i x.1 - j x.2 - (i x.1 - A' (j x.2)) + s x.1 = _
      abel
    have hE : (e' : X →L[F] R) =
        s.comp (ContinuousLinearMap.fst F S W) +
          (A' - ContinuousLinearMap.id F R).comp (j.comp (ContinuousLinearMap.snd F S W)) :=
      ContinuousLinearMap.ext he'
    rw [hE]
    exact hder
  have hψ₀ : ψ 0 = 0 := twistedOrbitAffineChart_zero A' j hf₀
  have hwpos : w t₀ ≠ 0 := (T.discriminantWeight_pos ⟨t₀.val, t₀.property.1⟩ (hDet ▸ hD.ne_zero)).ne'
  have hξmap : η.map e' = (w t₀)⁻¹ • ξ := by
    have hδmap := map_linearEquiv_residueAbsolute F ξ D'
    have hdet' : D'.toLinearEquiv.toLinearMap.det = D.det := by
      congr 1
      exact LinearMap.ext hD'
    rw [hdet', hDet] at hδmap
    change ξ.map D' = (w t₀)⁻¹ • ξ at hδmap
    change η.map (D' ∘ e ∘ ε) = _
    rw [← Measure.map_map D'.continuous.measurable (e.continuous.measurable.comp ε.continuous.measurable),
      ← Measure.map_map e.continuous.measurable ε.continuous.measurable, hε]
    exact hδmap
  obtain ⟨rψ, hrψ, hψball⟩ := exists_strictDerivative_ballChart η ψ e' hψd hψ₀
  obtain ⟨V₀, hV₀o, ht₀, hV₀w⟩ := hw.exists_open t₀
  let V₁ := (Homeomorph.mulRight t₀.val) ⁻¹' ((Subtype.val : A → T.val) '' V₀)
  have hV₁ : IsOpen V₁ := (hAo.isOpenEmbedding_subtypeVal.isOpenMap _ hV₀o).preimage
    (Homeomorph.mulRight t₀.val).continuous
  have hV₁₁ : (1 : T.val) ∈ V₁ := by
    change (1 : T.val) * t₀.val ∈ (Subtype.val : A → T.val) '' V₀
    rw [one_mul]
    exact mem_image_of_mem _ ht₀
  have hnear : (aT '' V₁) ∩ {x : S | ∃ y : A,
      y.val.val.val = (1 + x.val) * t₀.val.val.val ∧ f x * δ.val = (lift y).val.val} ∈ 𝓝 0 :=
    inter_mem ((haT.isOpenMap _ hV₁).mem_nhds (by
      rw [← T.affineCoordinate_one hT]; exact mem_image_of_mem aT hV₁₁)) hflocal
  obtain ⟨rS, hrS, hnS⟩ := Metric.mem_nhds_iff.mp hnear
  have hnear' : e' ⁻¹' (unitAffine '' (K₀ : Set G)) ∈ 𝓝 (0 : X) :=
    ((hiB.isOpenMap _ K₀.isOpen).preimage e'.continuous).mem_nhds (by
      change e' 0 ∈ unitAffine '' (K₀ : Set G)
      rw [map_zero, ← unitAffine_one (R := R)]
      exact mem_image_of_mem _ K₀.one_mem)
  obtain ⟨rO, hrO, hnO⟩ := Metric.mem_nhds_iff.mp hnear'
  let r := min rK (min rφ (min rψ (min rS rO))) / 2
  have hr₀ : 0 < min rK (min rφ (min rψ (min rS rO))) := lt_min hrK (lt_min hrφ (lt_min hrψ (lt_min hrS hrO)))
  have hr : 0 < r := half_pos hr₀
  have hrl := half_lt_self hr₀
  change r < min rK (min rφ (min rψ (min rS rO))) at hrl
  simp only [lt_min_iff] at hrl
  obtain ⟨hrK', hrφ', hrψ', hrS', hrO'⟩ := hrl
  let BS := closedBall (0 : S) r
  let BW := closedBall (0 : W) r
  let B := BS ×ˢ BW
  have hB : B = closedBall (0 : X) r := closedBall_prod_same 0 0 r
  have hψdata : IsOpenEmbedding (ψ ∘ (Subtype.val : B → X)) ∧
      ψ '' B = e' '' B ∧ (η.restrict B).map ψ = (η.map e').restrict (e' '' B) := by
    rw [hB]
    exact hψball r hr hrψ'.le
  obtain ⟨hψe', hψR, hψM⟩ := hψdata
  have hBS : MeasurableSet BS := isClosed_closedBall.measurableSet
  have hBW : MeasurableSet BW := isClosed_closedBall.measurableSet
  let : IsFiniteMeasure (ξS.comap (Subtype.val : BS → S)) :=
    isFiniteMeasure_comap_subtype_of_isCompact ξS hBS (isCompact_closedBall _ _)
  let : IsFiniteMeasure (ξW.comap (Subtype.val : BW → W)) :=
    isFiniteMeasure_comap_subtype_of_isCompact ξW hBW (isCompact_closedBall _ _)
  have hSB : BS ⊆ (aT '' V₁) ∩ {x : S | ∃ y : A,
      y.val.val.val = (1 + x.val) * t₀.val.val.val ∧ f x * δ.val = (lift y).val.val} :=
    (closedBall_subset_ball hrS').trans hnS
  have hOrbitR : e' '' B ⊆ unitAffine '' (K₀ : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hnO (closedBall_subset_ball hrO' (hB ▸ hx))
  obtain ⟨K, hKc, hKr⟩ := hKs r hr hrK'.le
  have hKr' : unitAffine '' (K : Set G) = e '' closedBall 0 r := by
    rw [← hKr, ← Subtype.range_coe (s := (K : Set G)), ← range_comp]
    rfl
  have hKK₀ : (K : Set G) ⊆ K₀ := by
    intro k hk
    have hm := mem_image_of_mem (unitAffine : G → R) hk
    rw [hKr'] at hm
    have hm' := image_mono (closedBall_subset_closedBall hrK'.le) hm
    rw [← hK₀] at hm'
    obtain ⟨k', hk', hh⟩ := hm'
    exact hiB.injective hh ▸ hk'
  have hμG : (μ.restrict (K : Set G)).map unitAffine =
      cG • ξ.restrict (e '' closedBall 0 r) := by
    rw [← hKr']
    exact map_restrict_subset_of_eq hiB.measurableEmbedding μ ξ K.isOpen.measurableSet hKK₀ hμG₀
  let KH := K.comap H.subtype continuous_subtype_val
  have hKH : (KH : Set H) = aH ⁻¹' BS := comap_unitAffine_ball e H aH haHG K hr.le hKr'
  let U := KH.comap eH.toMonoidHom eH.continuous
  have haComp : aH ∘ eH = aT := funext fun x => congrArg aT (eH.symm_apply_apply x)
  have hUB : (U : Set T.val) = aT ⁻¹' BS := by
    change eH ⁻¹' (KH : Set H) = _
    rw [hKH, ← preimage_comp, haComp]
  have hAr : BS ⊆ range aT := fun x hx => image_subset_range _ _ (hSB hx).1
  have hHr : BS ⊆ range aH := by
    intro x hx
    obtain ⟨u, rfl⟩ := hAr hx
    exact ⟨eH u, congrFun haComp u⟩
  have hUI : aT '' (U : Set T.val) = BS := by rw [hUB, image_preimage_eq_of_subset hAr]
  have hUc : IsCompact (U : Set T.val) := haT.isEmbedding.isCompact_iff.mpr (by
    rw [hUI]
    exact isCompact_closedBall _ _)
  have hUV₁ : (U : Set T.val) ⊆ V₁ := by
    intro u hu
    have huB : aT u ∈ BS := by
      change u ∈ aT ⁻¹' BS
      rw [← hUB]
      exact hu
    obtain ⟨v, hv, hEq⟩ := (hSB huB).1
    exact haT.injective hEq ▸ hv
  have hUA (u : T.val) (hu : u ∈ U) : u * t₀.val ∈ A := by
    obtain ⟨y, _, hy⟩ := hUV₁ hu
    change y.val = u * t₀.val at hy
    exact hy ▸ y.property
  obtain ⟨cS, hcS, hμS⟩ := T.exists_affineCoordinate_haar hT U hUc μT ξS
  rw [hUI] at hμS
  have hμHa : (μH.restrict (KH : Set H)).map aH = cS • ξS.restrict BS := by
    have hEq := eH.toHomeomorph.measurableEmbedding.restrict_map μT (KH : Set H)
    change (μT.map eH).restrict (KH : Set H) = (μT.restrict (U : Set T.val)).map eH at hEq
    rw [hμH'] at hEq
    rw [hEq, Measure.map_map haH.continuous.measurable hHe, haComp, hμS]
  obtain ⟨hφe, hφr, hφm⟩ := hφ r hr hrφ'.le
  obtain ⟨k, hk, hc₀, hc₀₀, hc₀m⟩ := affineQuotientChart e H hH μ μH ν hν aH haH haH₀ haHG
    ξS ξW K hKc cG cS hcS hr hKr' hHr hμG hμHa hφe hφr hφm
  let c₀ : BW → Q := fun y => leftQuotientMap H (k y : G)
  let c : BW → Q := rightTranslate H g ∘ c₀
  have hc : IsOpenEmbedding c := (rightTranslate H g).isOpenEmbedding.comp hc₀
  have hcval (x : BW) : c x = leftQuotientMap H ((k x : G) * g) := rfl
  have hcm : ((cG / cS) • ξW.comap Subtype.val).map c = ν.restrict (range c) := by
    change _ = ν.restrict (range (rightTranslate H g ∘ c₀))
    rw [Measure.map_map (rightTranslate H g).continuous.measurable hc₀.continuous.measurable |>.symm,
      hc₀m, map_restrict_image_of_embedding (rightTranslate H g).measurableEmbedding,
      (hν.right_invariant g).map_eq, range_comp]
  obtain ⟨t, ht, htval, htm⟩ := T.exists_regularNormAffineHaar hT ha μT ξS cS U hUI hμS t₀ hAo hUA
  have hty (x : BS) : (t x).val ∈ (Subtype.val : A → T.val) '' V₀ := by
    have hx := (hSB x.property).1
    obtain ⟨u, hu, heq⟩ := hx
    have hv : u.val.val = 1 + x.val.val := eq_add_of_sub_eq'
      (show u.val.val - 1 = x.val.val from congrArg (fun y : S => y.val) heq)
    have hh : (u * t₀.val : T.val) = (t x).val := by
      apply Subtype.ext
      apply Units.ext
      change u.val.val * t₀.val.val.val = _
      rw [hv, htval]
    exact hh ▸ hu
  have hwt (x : BS) : w (t x) = w t₀ := by
    obtain ⟨y, hy, hey⟩ := hty x
    exact (Subtype.ext hey : y = t x) ▸ hV₀w y hy
  have htz : t ⟨0, mem_closedBall_self hr.le⟩ = t₀ := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    simp [htval]
  have hft (x : BS) : f x.val * δ.val = (lift (t x)).val.val := by
    obtain ⟨y, hy, hfy⟩ := (hSB x.property).2
    have hy' : y = t x := Subtype.ext (Subtype.ext (Units.ext (hy.trans (htval x).symm)))
    exact hy' ▸ hfy
  let z : B → Q × A := fun x => (c ⟨x.val.2, x.property.2⟩, t ⟨x.val.1, x.property.1⟩)
  let V := range z
  have hVt : MeasurableSet (range c ×ˢ range t) := hc.isOpen_range.measurableSet.prod ht.isOpen_range.measurableSet
  obtain ⟨hz, hzR, hzm⟩ := weightedProductChart hBS hBW ξS ξW ν τ hc ht hc.continuous.measurable
    ht.continuous.measurable (cG / cS) cS hcm htm w (w t₀) hwt hVt
  change IsOpenEmbedding z at hz
  change V = _ at hzR
  have hsource : ((w t₀ * cG) • η.comap (Subtype.val : B → X)).map z = ρ.restrict V := by
    change _ = ((ν.prod τ).withDensity fun x : Q × A => (w x.2 : ENNReal)).restrict V
    rw [hzR]
    simpa only [η, z, mul_div_cancel₀ _ hcS.ne'] using hzm
  have hz₀ : (leftQuotientMap H g, t₀) ∈ V := by
    refine ⟨⟨0, mem_closedBall_self hr.le, mem_closedBall_self hr.le⟩, ?_⟩
    change (rightTranslate H g (c₀ ⟨0, mem_closedBall_self hr.le⟩), t ⟨0, mem_closedBall_self hr.le⟩) = _
    change c₀ ⟨0, mem_closedBall_self hr.le⟩ = leftQuotientMap H 1 at hc₀₀
    rw [hc₀₀, htz]
    change (leftQuotientMap H (1 * g), t₀) = _
    rw [one_mul]
  let m : G ≃ₜ G := (Homeomorph.mulLeft g).trans
    ((Homeomorph.mulRight (entrywiseAut σ n g)⁻¹).trans (Homeomorph.mulRight δ⁻¹))
  have hμm : μ.map m = μ := by
    have h := (measurePreserving_mul_right μ δ⁻¹).comp
      ((measurePreserving_mul_right μ (entrywiseAut σ n g)⁻¹).comp (measurePreserving_mul_left μ g))
    exact h.map_eq
  have hcomp : unitAffine ∘ m ∘ orbit ∘ z = ψ ∘ (Subtype.val : B → X) := by
    funext x
    let xS : BS := ⟨x.val.1, x.property.1⟩
    let xW : BW := ⟨x.val.2, x.property.2⟩
    let u : G := (k xW : G)
    change unitAffine (m (orbit (c xW, t xS))) = ψ x.val
    rw [hcval, show orbit (leftQuotientMap H (u * g), t xS) =
      (u * g)⁻¹ * (lift (t xS)).val * entrywiseAut σ n (u * g) from rfl]
    have hm : m ((u * g)⁻¹ * (lift (t xS)).val * entrywiseAut σ n (u * g)) =
        u⁻¹ * (lift (t xS)).val * entrywiseAut σ n u * δ⁻¹ := by
      change (g * ((u * g)⁻¹ * (lift (t xS)).val * entrywiseAut σ n (u * g))) *
        (entrywiseAut σ n g)⁻¹ * δ⁻¹ = _
      rw [map_mul, mul_inv_rev]
      simp [mul_assoc]
    rw [hm]
    have hu : u.val = 1 + j xW.val := hk xW
    have hAu : 1 + A' (j xW.val) = (δ * entrywiseAut σ n u * δ⁻¹).val := by
      change 1 + Aδ (j xW.val) = _
      rw [show (1 : R) = Aδ 1 from (map_one Aδ).symm, ← map_add, ← hu]
      rfl
    change (u⁻¹ * (lift (t xS)).val * entrywiseAut σ n u * δ⁻¹).val - 1 =
      Ring.inverse (1 + j xW.val) * f xS.val * (1 + A' (j xW.val)) - 1
    rw [← hu, Ring.inverse_unit, hAu]
    change (u⁻¹ : G).val * (lift (t xS)).val.val * (entrywiseAut σ n u).val * (δ⁻¹ : G).val - 1 =
      (u⁻¹ : G).val * f xS.val * (δ.val * (entrywiseAut σ n u).val * (δ⁻¹ : G).val) - 1
    rw [← hft xS]
    simp only [mul_assoc]
  have hψR' : range (ψ ∘ (Subtype.val : B → X)) = e' '' B := by
    rw [range_comp, Subtype.range_coe, hψR]
  have hψmeas : AEMeasurable ψ (η.restrict B) :=
    (aemeasurable_restrict_iff_comap_subtype (hBS.prod hBW)).mpr
      hψe'.continuous.measurable.aemeasurable
  have hψM' : ((w t₀ * cG) • η.restrict B).map ψ = cG • ξ.restrict (e' '' B) := by
    rw [Measure.map_smul _ hψmeas, hψM, hξmap, Measure.restrict_smul, smul_smul,
      mul_assoc, mul_comm cG _, ← mul_assoc, mul_inv_cancel₀ hwpos, one_mul]
  obtain ⟨hbranch, hpush⟩ := localPushforward_of_affine_chart (hBS.prod hBW) η ξ μ ρ hz orbit m hμm
    hiB cG (w t₀ * cG) hμG₀ ψ hψe' hcomp (e' '' B) hψR' hOrbitR hψM' hsource
  exact ⟨V, hz₀, hz.isOpen_range, hbranch, hpush⟩

end Langlands.BaseChange
