import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOppositeLevelSetMeasureBoundStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RestrictedOpenCellGamma
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OpenCellPoints
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrable
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalModulusFactorization
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnipotentHeightVolume
import Langlands.Representation.Aubert.General.DynamicOppositeHaarReciprocity
import Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityProof
import Langlands.Group.GL.LeviCentralQuotientMeasure
import Langlands.Analysis.Local.SiegelSetMeasure
import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination
import Langlands.BruhatTits.Unipotent.CompactOpenContainmentProof
import Langlands.BruhatTits.Unipotent.CocharacterContraction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOppositeLevelChartEntry
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOppositeModulusLevelDataProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOppositeWeightContractionProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TemperedTwistIntegrability
import Langlands.BruhatTits.SpecialCompact.CompatibleComponent
import Langlands.Representation.Aubert.General.RationalWeakChamberVolume

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Measure Topology
open scoped CategoryTheory.MonObj ENNReal NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.MatrixRepresentation
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.BruhatTits.SpecialCompact
open Langlands.GroupScheme.SplitTorusValuation (uniformizerUnit)

namespace Langlands.HarishChandraSchwartz

section CompactChart

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  {K P V : Subgroup H} [LocallyCompactSpace P] [LocallyCompactSpace V]

private theorem exists_compactChart_lintegral_le
    (hK : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H))
    (hH : ∀ h : H, modularCharacter h = 1)
    (hcell : IsOpenEmbedding (openCellMap (P := P) (V := V)))
    (μV : Measure V) [μV.IsHaarMeasure]
    (D : Set P) (B : Set V) (hD : MeasurableSet D) (hB : MeasurableSet B)
    (hDB : ∀ p ∈ D, ∀ v ∈ B, (p : H) * (v : H)⁻¹ ∈ K) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
    ∃ c : ℝ≥0, 0 < c ∧
      ∀ f : H → ℝ, Continuous f → (∀ x, 0 ≤ f x) →
        c * (∫⁻ p in D, ∫⁻ v in B, ENNReal.ofReal (f ((p : H) * (v : H)⁻¹))
          ∂μV ∂(haar : Measure P)) ≤
          ENNReal.ofReal (∫ k : K, f k ∂normalizedHaar K) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let C : TopologicalSpace.PositiveCompacts H :=
    ⟨⟨K, hKc⟩, by rw [hK.interior_eq]; exact ⟨1, K.one_mem⟩⟩
  let μG : Measure H := haarMeasure C
  have hmass : μG (K : Set H) = 1 := haarMeasure_self
  have hright (v : V) : Measure.map (fun g : H => g * (v : H)) μG = μG := by
    rw [ModularCompactAverage.map_mul_right_eq_modularCharacter_smul, hH, one_smul]
  let : SecondCountableTopology P := TopologicalSpace.Subtype.secondCountableTopology _
  let : SecondCountableTopology V := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨c, hc, heq⟩ := exists_lintegral_range_openCellMap_of_rightInvariantOn
    μG (haar : Measure P) μV hright hcell
  refine ⟨c, hc, fun f hf hnonneg => ?_⟩
  let F := (K : Set H).indicator (fun x => ENNReal.ofReal (f x))
  have hF : Measurable F := hf.measurable.ennreal_ofReal.indicator hK.measurableSet
  have htotal : ∫⁻ g, F g ∂μG = ENNReal.ofReal (∫ k : K, f k ∂normalizedHaar K) := by
    rw [lintegral_indicator hK.measurableSet, ← lintegral_subtype_comap hK.measurableSet]
    change (∫⁻ k : K, ENNReal.ofReal (f k) ∂(μG.comap ((↑) : K → H))) = _
    rw [comap_subtype_eq_smul_normalizedHaar hK μG, hmass, one_smul]
    have hfi : Integrable (fun k : K => f (k : H)) (normalizedHaar K) :=
      (hf.comp continuous_subtype_val).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    exact (ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ fun k => hnonneg k)).symm
  rw [← htotal]
  calc
    _ ≤ c * ∫⁻ p, ∫⁻ v, F ((p : H) * (v : H)⁻¹) ∂μV ∂(haar : Measure P) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le : 0 ≤ (c : ℝ≥0∞))
      calc
        _ ≤ ∫⁻ p in D, ∫⁻ v, F ((p : H) * (v : H)⁻¹) ∂μV ∂(haar : Measure P) := by
          refine setLIntegral_mono' hD (fun p hp => ?_)
          calc
            _ = ∫⁻ v in B, F ((p : H) * (v : H)⁻¹) ∂μV :=
              setLIntegral_congr_fun hB fun v hv => (Set.indicator_of_mem (hDB p hp v hv) _).symm
            _ ≤ ∫⁻ v, F ((p : H) * (v : H)⁻¹) ∂μV :=
              lintegral_mono' Measure.restrict_le_self le_rfl
        _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ g in Set.range (openCellMap (P := P) (V := V)), F g ∂μG := (heq F hF).symm
    _ ≤ ∫⁻ g, F g ∂μG := lintegral_mono' Measure.restrict_le_self le_rfl

private theorem exists_compactChart_level_bound [T2Space H]
    {P₀ M U : Subgroup H} (hPK : IsIwasawaPair P₀ K) (δ : P₀ →* ℝ≥0ˣ)
    (hδ : ∀ p : P₀, (p : H) ∈ K → δ p = 1)
    (hKo : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H))
    (hPc : IsClosed (P : Set H)) (hVc : IsClosed (V : Set H))
    (hH : ∀ h : H, modularCharacter h = 1)
    (hcell : IsOpenEmbedding (openCellMap (P := P) (V := V)))
    (hP : IsSemidirectDecomposition P M U) (hproj : Continuous hP.projection)
    (hU : U ≤ P₀) (hM : M ≤ Subgroup.normalizer (V : Set H))
    (μV : Measure V) [μV.IsHaarMeasure] [μV.Regular] [μV.IsInvInvariant] :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ (a : P₀) (ha : (a : H) ∈ M),
        (∀ m : M, Commute (a : H) (m : H)) →
        HaarModulus.normalizerCharacter V ⟨a, hM ha⟩ * δ a = 1 →
        ∀ (E : Set V), MeasurableSet E →
          (∀ x ∈ E, (a : H)⁻¹ * (x : H) * a ∈ K) →
          ∀ r : ℝ, 0 ≤ r → (∀ x ∈ E, iwasawaWeight hPK δ (x : H) = r) →
            c * ENNReal.ofReal ((NNReal.sqrt (δ a : ℝ≥0) : ℝ) * r) * μV E ≤
              ENNReal.ofReal (xi hPK δ ((a : H)⁻¹)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let D : Set P := ((↑) : P → H) ⁻¹' (K : Set H) ∩
    (fun p : P => (hP.projection p : H)) ⁻¹' (K : Set H)
  let B : OpenSubgroup V := ⟨K.comap V.subtype, hKo.preimage continuous_subtype_val⟩
  have hcont : Continuous (fun p : P => (hP.projection p : H)) :=
    continuous_subtype_val.comp hproj
  have hDo : IsOpen D := (hKo.preimage continuous_subtype_val).inter (hKo.preimage hcont)
  have hDc : IsCompact D :=
    (hPc.isClosedEmbedding_subtypeVal.isCompact_preimage hKc).inter_right
      (hKc.isClosed.preimage hcont)
  have hDnz : (haar : Measure P) D ≠ 0 :=
    hDo.measure_ne_zero _ ⟨1, K.one_mem, by
      change (hP.projection 1 : H) ∈ K
      rw [map_one]
      exact K.one_mem⟩
  have hBcompact : IsCompact (B : Set V) := hVc.isClosedEmbedding_subtypeVal.isCompact_preimage hKc
  have hBconj (g : Subgroup.normalizer (V : Set H)) (hg : (g : H) ∈ K) :
      HaarModulus.normalizerConj V g ⁻¹' (B : Set V) = B := by
    ext v
    change ((HaarModulus.normalizerConj V g v : V) : H) ∈ K ↔ (v : H) ∈ K
    rw [HaarModulus.normalizerConj_apply, K.mul_mem_cancel_right (K.inv_mem hg),
      K.mul_mem_cancel_left hg]
  obtain ⟨c, hc, hcineq⟩ := exists_compactChart_lintegral_le hKo hKc hH hcell μV D
    (B : Set V) hDo.measurableSet B.isOpen.measurableSet
    (fun p hp v hv => K.mul_mem hp.1 (K.inv_mem hv))
  refine ⟨(c : ℝ≥0∞) * (haar : Measure P) D, mul_ne_zero (by exact_mod_cast hc.ne') hDnz,
    ENNReal.mul_ne_top ENNReal.coe_ne_top hDc.measure_lt_top.ne, fun a ha hcomm hrecip E hE
      hentry r hr hw => ?_⟩
  let an : Subgroup.normalizer (V : Set H) := ⟨a, hM ha⟩
  let translatedWeight : ℝ := (NNReal.sqrt (δ a⁻¹ : ℝ≥0) : ℝ) * r
  have hcoef : ENNReal.ofReal translatedWeight * ((δ a : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal ((NNReal.sqrt (δ a : ℝ≥0) : ℝ) * r) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by dsimp [translatedWeight]; positivity)]
    congr 1
    have hsq : (NNReal.sqrt (δ a : ℝ≥0) : ℝ) * (NNReal.sqrt (δ a : ℝ≥0) : ℝ) =
        (δ a : ℝ≥0) := by exact_mod_cast NNReal.mul_self_sqrt (δ a : ℝ≥0)
    have hpos : 0 < (NNReal.sqrt (δ a : ℝ≥0) : ℝ) := by
      exact_mod_cast NNReal.sqrt_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero (δ a)))
    dsimp only [translatedWeight]
    rw [map_inv, Units.val_inv_eq_inv_val, NNReal.sqrt_inv, NNReal.coe_inv, ← hsq]
    field_simp
  have hinner (p : P) (hp : p ∈ D) :
      ENNReal.ofReal ((NNReal.sqrt (δ a : ℝ≥0) : ℝ) * r) * μV E ≤
        ∫⁻ v in (B : Set V), ENNReal.ofReal
          (iwasawaWeight hPK δ (((p : H) * (v : H)⁻¹) * (a : H)⁻¹)) ∂μV := by
    let m := hP.projection p
    have hmK : (m : H) ∈ K := hp.2
    let mn : Subgroup.normalizer (V : Set H) := ⟨m, hM m.2⟩
    let e := HaarModulus.normalizerConj V (an * mn)
    -- The preimage gives a subset of the compact chart where the weight is constant.
    let Q : Set V := (fun v : V => e v⁻¹) ⁻¹' E
    have hQ : MeasurableSet Q := hE.preimage (e.continuous_toFun.comp continuous_inv).measurable
    have hQB : Q ⊆ (B : Set V) := by
      intro v hv
      have hn := hentry (e v⁻¹) hv
      have heq : (a : H)⁻¹ * (e v⁻¹ : H) * a = (m : H) * (v : H)⁻¹ * (m : H)⁻¹ := by
        simp only [e, HaarModulus.normalizerConj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
        change (a : H)⁻¹ * (((a : H) * m) * (v : H)⁻¹ * ((a : H) * m)⁻¹) * a = _
        group
      rw [heq, K.mul_mem_cancel_right (K.inv_mem hmK), K.mul_mem_cancel_left hmK] at hn
      exact K.inv_mem_iff.mp hn
    have hmodm := HaarModulus.normalizerCharacter_eq_one_of_preimage V B hBcompact mn
      (hBconj mn hmK)
    have hmod : (mulEquivHaarChar e)⁻¹ = (δ a : ℝ≥0) := by
      have heq : HaarModulus.normalizerCharacter V (an * mn) * δ a = 1 := by
        rw [map_mul, hmodm, mul_one]
        exact hrecip
      have he := inv_eq_of_mul_eq_one_right heq
      rw [← Langlands.SiegelSetMeasure.mulEquivHaarChar_congr
        (@BorelSpace.mk V _ (borel V) rfl) inferInstance e]
      change ((HaarModulus.normalizerCharacter V (an * mn) : ℝ≥0))⁻¹ = _
      rw [← Units.val_inv_eq_inv_val, he]
    have hmass : μV Q = ((δ a : ℝ≥0) : ℝ≥0∞) * μV E := by
      rw [show Q = Inv.inv ⁻¹' (e ⁻¹' E) from rfl, measure_preimage_inv,
        measure_preimage_mulEquiv μV, hmod]
    have huU : (p : H) * (m : H)⁻¹ ∈ U := by
      have h := (Subgroup.mem_normalizer_iff.mp (hP.levi_le_normalizer m.2) _).mp
        (hP.projection_inv_mul_mem p)
      change (m : H) * ((m : H)⁻¹ * (p : H)) * (m : H)⁻¹ ∈ U at h
      simpa only [mul_inv_cancel_left] using h
    let u : P₀ := ⟨(p : H) * (m : H)⁻¹, hU huU⟩
    have huK : (u : H) ∈ K := K.mul_mem hp.1 (K.inv_mem hmK)
    have hweight (v : V) (hv : v ∈ Q) :
        iwasawaWeight hPK δ (((p : H) * (v : H)⁻¹) * (a : H)⁻¹) = translatedWeight := by
      have heq : ((p : H) * (v : H)⁻¹) * (a : H)⁻¹ =
          (u : H) * ((a⁻¹ : P₀) * (e v⁻¹ : H)) * m := by
        calc
          _ = (p : H) * (v : H)⁻¹ * ((m : H)⁻¹ * (a : H)⁻¹ * m) := by
            rw [(hcomm m).inv_inv.eq.symm]
            group
          _ = _ := by
            simp only [u, e, HaarModulus.normalizerConj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
            change _ = ((p : H) * (m : H)⁻¹) *
              ((a : H)⁻¹ * (((a : H) * m) * (v : H)⁻¹ * ((a : H) * m)⁻¹)) * m
            group
      rw [heq, iwasawaWeight_mul_right hδ _ hmK, iwasawaWeight_mul_left hδ u,
        hδ u huK, Units.val_one, NNReal.sqrt_one, NNReal.coe_one, one_mul,
        iwasawaWeight_mul_left hδ a⁻¹, hw _ hv]
    calc
      _ = ENNReal.ofReal translatedWeight * μV Q := by rw [hmass, ← mul_assoc, hcoef]
      _ = ∫⁻ v in Q, ENNReal.ofReal
          (iwasawaWeight hPK δ (((p : H) * (v : H)⁻¹) * (a : H)⁻¹)) ∂μV := by
        rw [setLIntegral_congr_fun hQ (fun v hv => congrArg ENNReal.ofReal (hweight v hv)),
          lintegral_const, Measure.restrict_apply_univ]
      _ ≤ _ := lintegral_mono_set hQB
  have houter :
      (∫⁻ _ in D, ENNReal.ofReal ((NNReal.sqrt (δ a : ℝ≥0) : ℝ) * r) * μV E
          ∂(haar : Measure P)) ≤
        ∫⁻ p in D, ∫⁻ v in (B : Set V), ENNReal.ofReal
          (iwasawaWeight hPK δ (((p : H) * (v : H)⁻¹) * (a : H)⁻¹)) ∂μV ∂(haar : Measure P) :=
    setLIntegral_mono' hDo.measurableSet hinner
  rw [lintegral_const, Measure.restrict_apply_univ] at houter
  have hcineq' := hcineq (fun g => iwasawaWeight hPK δ (g * (a : H)⁻¹))
    ((continuous_iwasawaWeight hδ hKo).comp (continuous_id.mul continuous_const))
    (fun g => iwasawaWeight_nonneg (g * (a : H)⁻¹))
  refine le_trans ?_ hcineq'
  calc
    _ = (c : ℝ≥0∞) * ((ENNReal.ofReal ((NNReal.sqrt (δ a : ℝ≥0) : ℝ) * r) * μV E) *
        (haar : Measure P) D) := by ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left houter (zero_le : 0 ≤ (c : ℝ≥0∞))

end CompactChart

section RationalChart

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {J : Set (characterLattice S)} {ζ : cocharacterLattice S} {K : Subgroup (rationalPoints G)}

private theorem exists_rationalOppositeLevel_chart_bound (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) (hζ : IsStandardCocharacter i ν J ζ)
    (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    (νU : Measure (oppositeUnipotent i ζ)) [νU.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ (t : Fˣ) (j : ℕ),
      let a : rationalPoints G := (gmRationalPoint t ≫ (CommGroupScheme.groupHom ζ ≫ i).hom.hom) ^ j
      ∃ ha : a ∈ standardParabolicPoints i ν ∅,
        ∀ (E : Set (oppositeUnipotent i ζ)), MeasurableSet E →
          (∀ x ∈ E, a⁻¹ * (x : rationalPoints G) * a ∈ K) →
          ∀ r : ℝ, 0 ≤ r →
            (∀ x ∈ E, iwasawaWeight hPK (rationalMinimalModulus i ν) (x : rationalPoints G) = r) →
            c * ENNReal.ofReal ((NNReal.sqrt (rationalMinimalModulus i ν ⟨a, ha⟩ : ℝ≥0) : ℝ) * r) * νU E ≤
              ENNReal.ofReal (rationalXi hKc hPK a) := by
  have := hG.smooth
  let : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  let : SecondCountableTopology (rationalPoints G) := rationalPoint_secondCountableTopology F G
  let : NonarchimedeanGroup (rationalPoints G) := Plancherel.rationalPoints_nonarchimedeanGroup G
  let χ := CommGroupScheme.groupHom ζ ≫ i
  let P := standardParabolicPoints i ν J
  let M := standardLeviPoints i ν J
  let U := standardUnipotentPoints i ν J
  let V := oppositeUnipotent i ζ
  let T := Over.mk (𝟙 (Spec (CommRingCat.of F)))
  have hJ := hζ.subset i ν
  obtain ⟨hPfun, hMfun, hUfun⟩ := ((standardCocharacter F G hG S i hi ν hν J hJ).2 ζ hζ)
  have hPeq : P = (Dynamic.parabolic χ).carrier T := congrArg (fun Q => Q.carrier T) hPfun
  have hMeq : M = (Dynamic.centralizer χ).carrier T := congrArg (fun Q => Q.carrier T) hMfun
  have hUeq : U = (Dynamic.unipotent χ).carrier T := congrArg (fun Q => Q.carrier T) hUfun
  have hPc : IsClosed (P : Set (rationalPoints G)) := by
    rw [hPeq]
    exact isClosed_rationalPoint_subgroup F _ _ (Dynamic.Affine.isRepresentedBy_parabolicHom χ)
      (Dynamic.Affine.isClosedSubgroup_parabolicHom χ)
  have hVc : IsClosed (V : Set (rationalPoints G)) := isClosed_oppositeUnipotent_localField i ζ
  let : LocallyCompactSpace P := hPc.locallyCompactSpace
  let : LocallyCompactSpace V := hVc.locallyCompactSpace
  let : SecondCountableTopology V := TopologicalSpace.Subtype.secondCountableTopology _
  have : νU.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure νU
  have hcompact (v : V) : ∃ H : OpenSubgroup V, IsCompact (H : Set V) ∧ v ∈ H := by
    obtain ⟨H, hHc, hv⟩ := BruhatTits.dynamicUnipotentCompactOpenContainment F G hG
      (Dynamic.inverseCocharacter χ) ({v} : Set V) isCompact_singleton
    exact ⟨H, hHc, hv (Set.mem_singleton v)⟩
  have : νU.IsMulRightInvariant := by
    constructor
    intro v
    obtain ⟨H, hHc, hv⟩ := hcompact v
    rw [ModularCompactAverage.map_mul_right_eq_modularCharacter_smul,
      ModularCompactAverage.modularCharacter_eq_one_of_mem H.toSubgroup H.isOpen hHc
        hv, one_smul]
  have : νU.IsInvInvariant := Langlands.isInvInvariant_of_isMulRightInvariant νU
  have hcell : IsOpenEmbedding (openCellMap (P := P) (V := V)) := by
    rw [hPeq]
    exact isOpenEmbedding_openCellMap_rationalPoint F G χ
  have hP : IsSemidirectDecomposition P M U := isSemidirectDecomposition_standard hG hi hν hJ
  have hproj := continuous_projection_standard hG hi hν hJ hP
  have hMU : M ≤ Subgroup.normalizer (U : Set (rationalPoints G)) := hP.levi_le_normalizer
  have hMV : M ≤ Subgroup.normalizer (V : Set (rationalPoints G)) := by
    rw [hMeq, ← Dynamic.centralizer_inverseCocharacter χ]
    exact Dynamic.centralizer_le_normalizer_unipotent (Dynamic.inverseCocharacter χ) T
  have hU₀ : U ≤ standardParabolicPoints i ν ∅ := fun g hg =>
    standardUnipotent_le_standardParabolic i ν ∅ T
      (standardUnipotentPoints_le_empty_of_subset hG hi hν hJ hg :
        g ∈ standardUnipotentPoints i ν ∅)
  obtain ⟨c, hc₀, hc₁, hc⟩ := exists_compactChart_level_bound hPK (rationalMinimalModulus i ν)
    (rationalMinimalModulus_eq_one i ν hKo hKc) hKo hKc hPc hVc
    (rationalPoints_modularCharacter_eq_one hG) hcell hP hproj hU₀ hMV νU
  refine ⟨c, hc₀, hc₁, fun t j => ?_⟩
  let a₁ : rationalPoints G := gmRationalPoint t ≫ χ.hom.hom
  have haP₁ : a₁ ∈ standardParabolicPoints i ν ∅ :=
    standardLevi_le_standardParabolic i ν ∅ _
      (map_mem_standardLeviPoints_empty (i := i) (ν := ν) (CommGroupScheme.groupHom ζ) (gmRationalPoint t))
  have haM₁ : a₁ ∈ M := by
    rw [hMeq]
    simpa only [cocharPoint_eq_gmRationalPoint_comp] using
      BruhatTits.DynamicUnipotentContainment.cocharPoint_mem_centralizer χ t
  let a := a₁ ^ j
  have haP : a ∈ standardParabolicPoints i ν ∅ := (standardParabolicPoints i ν ∅).pow_mem haP₁ j
  have haM : a ∈ M := M.pow_mem haM₁ j
  have haComm (m : M) : Commute a (m : rationalPoints G) := by
    have hm : (m : rationalPoints G) ∈ (Dynamic.centralizer χ).carrier T := hMeq.le m.2
    exact (Dynamic.commute_cocharacter_of_mem_centralizer χ hm (gmRationalPoint t)).symm.pow_left j
  let aP : standardParabolicPoints i ν ∅ := ⟨a, haP⟩
  let aM : M := ⟨a, haM⟩
  have hdelta := rationalMinimalModulus_eq_standardUnipotentModulus_of_commute hG hi hν hJ
    ⟨a, Subgroup.mem_inf.mpr ⟨haP, haM⟩⟩ (fun m hm => (haComm ⟨m, hm⟩).eq)
  have hrecip : HaarModulus.normalizerCharacter V ⟨a, hMV haM⟩ * rationalMinimalModulus i ν aP = 1 := by
    rw [hdelta]
    exact dynamicOppositeHaarReciprocity_of_leviAdjoint Dynamic.leviAdjointDeterminantReciprocity
      hG χ V M U rfl hMeq hUeq hVc (isClosed_standardUnipotentPoints i ν J) hMV hMU aM
  refine ⟨haP, fun E hE hentry r hr hw => ?_⟩
  have hb := hc aP haM haComm hrecip E hE hentry r hr hw
  change _ ≤ ENNReal.ofReal (rationalXi hKc hPK a⁻¹) at hb
  rw [rationalXi_inv hG hi hν hKo hKc hPK] at hb
  exact hb


set_option maxHeartbeats 600000 in
private theorem cocharacter_uniformizer_pow_mem_minimal_chamber (hi : IsMaximalSplitTorus i)
    (hζ : IsStandardCocharacter i ν J ζ)
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
    (hA : IsCompatibleStandardSplitComponent i ν ∅ A q) :
    let a : rationalPoints G := gmRationalPoint (uniformizerUnit F) ≫
      (CommGroupScheme.groupHom ζ ≫ i).hom.hom
    ∀ m : ℕ, a ^ m ∈ standardComponentCAplus i ν ∅ q := by
  let t := uniformizerUnit F
  let a : rationalPoints G := gmRationalPoint t ≫ (CommGroupScheme.groupHom ζ ≫ i).hom.hom
  have haTor : uniformizerPowers i (Multiplicative.ofAdd ζ) = a := by
    change ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm t ≫
      (CommGroupScheme.groupHom ζ).hom.hom) ≫ i.hom.hom = _
    rw [Category.assoc, ← Grp.comp_hom_hom]
    rw [← BruhatTits.DynamicUnipotentContainment.cocharPoint_eq (CommGroupScheme.groupHom ζ ≫ i) t]
    exact cocharPoint_eq_gmRationalPoint_comp (CommGroupScheme.groupHom ζ ≫ i) t
  have hnonneg (β : SimpleRoot i ν) : 0 ≤ simpleRootPairing i ν β ζ := by
    by_cases hβ : β.1 ∈ J
    · exact (hζ.2.1 _ hβ).ge
    · exact (hζ.2.2 _ β.2 hβ).le
  change ∀ m : ℕ, a ^ m ∈ standardComponentCAplus i ν ∅ q
  intro m
  have hh := uniformizerPowers_mem_standardComponentCAplus i ν hi
    (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν) ∅
    (by rw [rootSet_empty]; exact ⟨ν, isStandardCocharacter_empty_self i ν⟩)
    q (by simpa only [rootSet_empty] using hA) (m • ζ) (by simp) (fun β _ => by
      rw [map_nsmul]
      exact nsmul_nonneg (hnonneg β) _)
  simpa only [rootSet_empty, ofAdd_nsmul, map_pow, haTor] using hh

set_option maxHeartbeats 800000 in
private theorem rationalOppositeLevelSetMeasureBound_of_inputs
    (hlevels : RationalOppositeModulusLevelDataStatement.{u})
    (hcontraction : RationalOppositeWeightContractionStatement.{u})
    (hupper : RationalXiUpperBoundStatement.{u}) : RationalOppositeLevelSetMeasureBoundStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν J ζ hζ K0 _ _ hbasis _ K hKo hPK hKc νU _ L hL hw
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let t := uniformizerUnit F
  let a : rationalPoints G := gmRationalPoint t ≫ (CommGroupScheme.groupHom ζ ≫ i).hom.hom
  let qF : ℝ := LocalField.residueCardinality F
  have hqF : 0 < qF := by
    change (0 : ℝ) < LocalField.residueCardinality F
    exact_mod_cast (zero_lt_one.trans (LocalField.residueCardinality_gt_one F))
  obtain ⟨b, hb⟩ := exists_oppositeLevel_chart_entry hcontraction hlevels hG hi hν hζ hKo hKc hw
    (hKo.mem_nhds K.one_mem)
  obtain ⟨c, hc₀, hcTop, hc⟩ := exists_rationalOppositeLevel_chart_bound hG hi hν hζ hKo hKc hPK νU
  obtain ⟨A, q, hA⟩ := exists_compatibleStandardSplitComponent hG i hi ν hν ∅ (Set.empty_subset _)
  obtain ⟨N, ρ, hρ⟩ := Plancherel.exists_isClosedSubgroup_fin_succ G
  obtain ⟨d, hd⟩ := hupper F G hG S i hi ν hν K0 hbasis A q hA K hKo hKc hPK (N + 1) ρ hρ
  obtain ⟨C, hC⟩ := hd 1 1
  have hChamber := cocharacter_uniformizer_pow_mem_minimal_chamber hi hζ hA
  let σ : rationalPoints G → ℝ := rationalHeight (F := F) ρ
  have hσ : 0 ≤ σ a := rationalHeight_nonneg ρ a
  let B : ℝ := 1 + (1 + (b : ℝ)) * σ a
  let M : ℝ := max C 1 * B ^ d
  have hcR : 0 < c.toReal := ENNReal.toReal_pos hc₀ hcTop
  refine ⟨c.toReal⁻¹ * M, (d : ℝ), fun n hn => ?_⟩
  let E : Set (oppositeUnipotent i ζ) := {x | L x = (n : ℤ)}
  let r : ℝ := qF ^ (-(n : ℝ) / 2)
  have hr : 0 < r := Real.rpow_pos_of_pos hqF _
  have htranslatedWeight : r * qF ^ ((n : ℝ) / 2) = 1 := by
    dsimp only [r]
    rw [← Real.rpow_add hqF, show -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 by ring, Real.rpow_zero]
  have hE : MeasurableSet E := hL (measurableSet_singleton (n : ℤ))
  obtain ⟨ha, hchart⟩ := hc t (n + b)
  change a ^ (n + b) ∈ standardParabolicPoints i ν ∅ at ha
  let s : ℝ := NNReal.sqrt (rationalMinimalModulus i ν ⟨a ^ (n + b), ha⟩ : ℝ≥0)
  have hs : 0 < s := by
    dsimp only [s]
    exact_mod_cast NNReal.sqrt_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hlow : c * ENNReal.ofReal (s * r) * νU E ≤
      ENNReal.ofReal (rationalXi hKc hPK (a ^ (n + b))) :=
    hchart E hE (fun x hx => hb n x hx) r hr.le (by
      intro x hx
      change L x = (n : ℤ) at hx
      rw [hw, hx, Int.cast_natCast])
  have hheight : (1 + σ (a ^ (n + b))) ^ d ≤ B ^ d * (n : ℝ) ^ d := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (zero_le_one.trans (le_add_of_nonneg_right (rationalHeight_nonneg ρ _)))
    have hp := le_add_nsmul_of_subadditive (rationalHeight_mul_le (F := F) ρ) a (n + b)
    change σ (a ^ (n + b)) ≤ σ 1 + ((n + b : ℕ) : ℝ) * σ a at hp
    rw [show σ 1 = 0 from rationalHeight_one ρ, zero_add, Nat.cast_add] at hp
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hbR : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have hm : (n : ℝ) + b ≤ (1 + (b : ℝ)) * n := by nlinarith
    dsimp only [B]
    nlinarith [mul_le_mul_of_nonneg_right hm hσ]
  have hup : rationalXi hKc hPK (a ^ (n + b)) ≤ s * (M * (n : ℝ) ^ d) := by
    have hh := hC (a ^ (n + b)) ha (hChamber (n + b))
    rw [one_mul, mul_one] at hh
    calc
      _ ≤ C * s * (1 + σ (a ^ (n + b))) ^ d := hh
      _ ≤ max C 1 * s * (1 + σ (a ^ (n + b))) ^ d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hs.le)
          (pow_nonneg (zero_le_one.trans (le_add_of_nonneg_right (rationalHeight_nonneg ρ _))) _)
      _ ≤ max C 1 * s * (B ^ d * (n : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left hheight (mul_nonneg (zero_le_one.trans (le_max_right _ _)) hs.le)
      _ = s * (M * (n : ℝ) ^ d) := by dsimp only [M]; ring
  change νU E ≤ ENNReal.ofReal (c.toReal⁻¹ * M * qF ^ ((n : ℝ) / 2) * (n : ℝ) ^ (d : ℝ))
  rw [Real.rpow_natCast]
  refine (ENNReal.mul_le_mul_iff_right (mul_ne_zero hc₀ (ENNReal.ofReal_pos.mpr (mul_pos hs hr)).ne')
    (ENNReal.mul_ne_top hcTop ENNReal.ofReal_ne_top)).1 ?_
  calc
    _ ≤ ENNReal.ofReal (rationalXi hKc hPK (a ^ (n + b))) := hlow
    _ ≤ ENNReal.ofReal (s * (M * (n : ℝ) ^ d)) := ENNReal.ofReal_le_ofReal hup
    _ = _ := by
      symm
      nth_rw 1 [← ENNReal.ofReal_toReal hcTop]
      rw [← ENNReal.ofReal_mul hcR.le,
        ← ENNReal.ofReal_mul (mul_nonneg hcR.le (mul_nonneg hs.le hr.le))]
      congr 1
      calc
        _ = (c.toReal * c.toReal⁻¹) * (r * qF ^ ((n : ℝ) / 2)) *
            (s * (M * (n : ℝ) ^ d)) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hcR.ne', htranslatedWeight, one_mul, one_mul]

end RationalChart

/-- Waldspurger II.4.1 for the actual opposite standard unipotent radical. -/
theorem rationalOppositeLevelSetMeasureBound : RationalOppositeLevelSetMeasureBoundStatement.{u} :=
  rationalOppositeLevelSetMeasureBound_of_inputs rationalOppositeModulusLevelData
    rationalOppositeWeightContraction rationalXiUpperBound

end Langlands.HarishChandraSchwartz
