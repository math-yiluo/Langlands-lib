import Langlands.Automorphic.BlockShapeSingleCutLeviQuotient

/-! # A single-block period of a constant term -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set Topology
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

open MeasureTheory.Measure

variable {G : Type u} {H : Type v} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
  [SecondCountableTopology G] [SecondCountableTopology H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  [MeasurableSpace G] [MeasurableSpace H] [BorelSpace G] [BorelSpace H]

/-- A continuous group isomorphism matching the lattices preserves the
normalized fundamental-domain period on compact left quotients. -/
theorem normalizedFundamentalDomainIntegral_eq_comp_equiv
    (e : G ≃ₜ* H) (Γ : Subgroup G) (Δ : Subgroup H)
    (hΓ : IsDiscrete (Γ : Set G)) (hΔ : IsDiscrete (Δ : Set H))
    [CompactSpace (Global.LeftCosetSpace Γ)]
    (he : ∀ x, e x ∈ Δ ↔ x ∈ Γ) (φ : H → ℂ)
    (hφ : ∀ δ ∈ Δ, ∀ x, φ (δ * x) = φ x) :
    normalizedFundamentalDomainIntegral Δ hΔ φ =
      normalizedFundamentalDomainIntegral Γ hΓ (φ ∘ e) := by
  let D := fundamentalDomain Γ hΓ
  let E := fundamentalDomain Δ hΔ
  let T := e.symm ⁻¹' D
  let haarG : Measure G := Measure.haar
  let haarH : Measure H := Measure.haar
  let a := haarScalarFactor haarH (haarG.map e)
  have hT : MeasurableSet T :=
    (measurableSet_fundamentalDomain Γ hΓ).preimage e.symm.continuous.measurable
  have hsymm (y : H) : e.symm y ∈ Γ ↔ y ∈ Δ := by
    simpa only [e.apply_symm_apply] using (he (e.symm y)).symm
  have hdomain : IsFundamentalDomain Δ T haarH := by
    refine IsFundamentalDomain.mk' hT.nullMeasurableSet fun y => ?_
    obtain ⟨γ, hγ, huniq⟩ := fundamentalDomain_unique Γ hΓ (e.symm y)
    refine ⟨⟨e γ, (he γ).mpr γ.property⟩, ?_, ?_⟩
    · change e.symm (e γ * y) ∈ D
      simpa only [map_mul, e.symm_apply_apply] using hγ
    · intro δ hδ
      change e.symm ((δ : H) * y) ∈ D at hδ
      rw [map_mul] at hδ
      have h := huniq ⟨e.symm δ, (hsymm δ).mpr δ.property⟩ hδ
      exact Subtype.ext (by
        simpa only [e.apply_symm_apply] using congrArg (fun γ : Γ => e γ.val) h)
  have : (haarG.map e).IsHaarMeasure := e.isHaarMeasure_map haarG
  have hhaarH : haarH = a • haarG.map e := isMulLeftInvariant_eq_smul _ _
  have heMeas : Measurable (e : G → H) := e.continuous.measurable
  have ha : (a : ℝ) ≠ 0 := by
    exact_mod_cast (haarScalarFactor_pos_of_isHaarMeasure haarH (haarG.map e)).ne'
  have hpre : e ⁻¹' T = D := by
    ext x
    simp only [T, mem_preimage, e.symm_apply_apply]
  have : Countable Δ := countable_of_isDiscrete Δ hΔ
  have hI : ∫ y in E, φ y ∂haarH = (a : ℝ) • ∫ x in D, φ (e x) ∂haarG := by
    rw [(isFundamentalDomain Δ hΔ haarH).setIntegral_eq hdomain (fun δ y => hφ δ δ.property y)]
    rw [hhaarH, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def]
    change (a : ℝ) • (∫ y in T, φ y ∂haarG.map e.toHomeomorph) = _
    rw [e.toHomeomorph.isClosedEmbedding.setIntegral_map]
    change (a : ℝ) • (∫ x in e ⁻¹' T, φ (e x) ∂haarG) = _
    rw [hpre]
  have hmass : haarH E = (a : ℝ≥0∞) * haarG D := by
    rw [(isFundamentalDomain Δ hΔ haarH).measure_eq hdomain, hhaarH, Measure.smul_apply,
      Measure.map_apply heMeas hT, hpre, ENNReal.smul_def, smul_eq_mul]
  have := isLocallyFiniteMeasure_haarQuotientMeasure Γ hΓ
  have hD : (haarG D).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr
    ⟨haar_fundamentalDomain_ne_zero Γ hΓ, haar_fundamentalDomain_ne_top Γ hΓ⟩
  unfold normalizedFundamentalDomainIntegral
  change (haarH E).toReal⁻¹ • (∫ y in E, φ y ∂haarH) = (haarG D).toReal⁻¹ • ∫ x in D, φ (e x) ∂haarG
  rw [hI, hmass, ENNReal.toReal_mul, ENNReal.coe_toReal, ← mul_smul]
  congr 1
  field_simp

end Langlands.Global.LeftCosetSpace

namespace Langlands.Automorphic

open scoped CategoryTheory.MonObj

open Langlands.GeneralLinear Langlands.Global Langlands.GroupScheme
  Langlands.GroupScheme.GeneralLinear AdelicSubgroupPoints GeneralLinearBlockSemidirect

variable {n : ℕ} (B : BlockShape n) (F : Type u) [Field F] [NumberField F]
  (i : Fin B.length) (c : Fin (B.size i - 1))

local notation "RF" => CommRingCat.of F
local notation "G" => GroupScheme.GeneralLinear.groupScheme (Fin n) RF
local notation "H" => GroupScheme.GeneralLinear.groupScheme (Fin (B.size i)) RF
local notation "w" => standardBlockWeight B.cuts
local notation "e" => standardBlockWeight (insert (blockShapeSingleCut B i c) B.cuts)
local notation "U" => blockUnipotent (Fin (B.size i)) RF (oneCutWeight c)
local notation "V" => leviUnipotent (Fin n) RF e w

local instance singleCutPeriodAffine (d : ℕ) : IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin d) RF).X.left :=
  isAffine_groupScheme (Fin d) RF

local instance singleCutPeriodSmooth (d : ℕ) : Smooth (GroupScheme.GeneralLinear.groupScheme (Fin d) RF).X.hom :=
  smoothStatement (Fin d) RF

local instance singleCutPeriodRationalAddCommGroup (d : ℕ) : AddCommGroup (RationalInvariantFunctions F d) := Submodule.addCommGroup _
local instance singleCutPeriodContinuousAddCommGroup (d : ℕ) : AddCommGroup (ContinuousRationalFunctions F d) := Submodule.addCommGroup _
local instance singleCutPeriodFiniteSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

private theorem blockUpdate_mulSingle (m : AdelicBlockParabolic.FullLevi F B)
    (y x : AdelicGL F (B.size i)) :
    Function.update m i (y * x) = Pi.mulSingle i y * Function.update m i x := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self, Pi.mul_apply, Pi.mulSingle_eq_same]
  · simp only [Function.update_of_ne hj, Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, one_mul]

/-- The normalized period of the individual Levi slice along the radical for
one cut inside its block. -/
def blockShapeSingleCutPeriod (f : FiniteSmoothRationalFunctions F n) (g : AdelicGL F n)
    (m : AdelicBlockParabolic.FullLevi F B) (x : AdelicGL F (B.size i)) : ℂ :=
  GroupSchemeFunctions.normalizedBlockConstantTerm F (oneCutWeight c)
    ((GroupSchemeFunctions.continuousGeneralLinearEquiv F (B.size i)).symm
      (blockShapeLeviSliceFactor B F f g m i))
    ((GeneralLinearGroupPoints.adelicEquiv F (B.size i)).symm x)

set_option maxHeartbeats 800000 in
/-- The period in a single block is the ambient constant term for the
refinement by the corresponding global cut. -/
theorem blockShapeSingleCutPeriod_eq_refined
    (f : FiniteSmoothRationalFunctions F n) (g : AdelicGL F n)
    (m : AdelicBlockParabolic.FullLevi F B) (x : AdelicGL F (B.size i)) :
    blockShapeSingleCutPeriod B F i c f g m x =
      finiteSmoothBlockConstantTerm F e f ((GeneralLinearGroupPoints.adelicEquiv F n).symm
        (B.leviEmbedding (Adeles F) (Function.update m i x) * g)) := by
  let a := GeneralLinearGroupPoints.adelicEquiv F n
  let b := GeneralLinearGroupPoints.adelicEquiv F (B.size i)
  let α := singleCutLeviAdelicEquiv B F i c
  let y := a.symm (B.leviEmbedding (Adeles F) (Function.update m i x) * g)
  let F₀ := (GroupSchemeFunctions.continuousGeneralLinearEquiv F n).symm f.val
  let s := blockShapeLeviSliceFactor B F f g m i
  let S := (GroupSchemeFunctions.continuousGeneralLinearEquiv F (B.size i)).symm s
  let φ : adelicPoints F G V → ℂ := fun d =>
    GroupSchemeFunctions.normalizedBlockConstantTerm F w F₀ (d.val * y)
  have hbase (t : AdelicGroupPoints F G) :
      GroupSchemeFunctions.normalizedBlockConstantTerm F w F₀ t =
        blockShapeConstantTerm B F f (a t) := by
    simp only [blockShapeConstantTerm, a, MulEquiv.symm_apply_apply,
      finiteSmoothBlockConstantTerm_apply, F₀]
  have hφ (d : adelicPoints F H U) : φ (α d) = s.val.val (b d.val * x) := by
    have harg : a ((α d).val * y) =
        B.leviEmbedding (Adeles F) (Function.update m i (b d.val * x)) * g := by
      rw [map_mul, singleCutLeviAdelicEquiv_val, a.apply_symm_apply, blockUpdate_mulSingle,
        map_mul, ← mul_assoc]
      rfl
    change GroupSchemeFunctions.normalizedBlockConstantTerm F w F₀ ((α d).val * y) = _
    rw [hbase, harg]
    rfl
  have hΓ (δ : adelicPoints F G V) (hδ : δ ∈ rationalSubgroup F G V) (d : adelicPoints F G V) :
      φ (δ * d) = φ d := by
    obtain ⟨p, rfl⟩ := α.surjective δ
    obtain ⟨q, rfl⟩ := α.surjective d
    have hp := (singleCutLeviAdelicEquiv_mem_rationalSubgroup_iff B F i c p).mp hδ
    obtain ⟨t, rfl⟩ := hp
    rw [← map_mul, hφ, hφ]
    change s.val.val (b ((AdelicSubgroupPoints.rational F H U t).val * q.val) * x) = _
    rw [map_mul, rational_coe, GeneralLinearGroupPoints.adelicEquiv_rational, mul_assoc]
    exact s.val.property (GeneralLinearGroupPoints.rationalEquiv F (B.size i) t.val) _
  have hw : ∀ a b, e a ≤ e b → w a ≤ w b :=
    standardBlockWeight_refines (cuts_ssubset_insert_blockShapeSingleCut B i c).subset
  let : LocallyCompactSpace (adelicPoints F H U) :=
    (isClosed_adelicPoints_blockUnipotent F (oneCutWeight c)).locallyCompactSpace
  let : LocallyCompactSpace (adelicPoints F G V) :=
    (isClosed_adelicPoints_leviUnipotent F e w).locallyCompactSpace
  let : CompactSpace (RationalQuotient F H U) :=
    GroupSchemeFunctions.blockUnipotentRationalQuotientCompactSpace F (oneCutWeight c)
  have ht := LeftCosetSpace.normalizedFundamentalDomainIntegral_eq_comp_equiv α
    (rationalSubgroup F H U) (rationalSubgroup F G V)
    (isDiscrete_rationalSubgroup F H U) (isDiscrete_rationalSubgroup F G V)
    (singleCutLeviAdelicEquiv_mem_rationalSubgroup_iff B F i c) φ hΓ
  have hS : (φ ∘ α) = fun d : adelicPoints F H U =>
      GroupSchemeFunctions.evaluate F H S (d.val * b.symm x) := by
    funext d
    change φ (α d) = s.val.val (b (d.val * b.symm x))
    rw [hφ, map_mul, b.apply_symm_apply]
  rw [hS] at ht
  change GroupSchemeFunctions.normalizedBlockConstantTerm F (oneCutWeight c) S (b.symm x) =
    GroupSchemeFunctions.normalizedBlockConstantTerm F e F₀ y
  rw [GroupSchemeFunctions.normalizedBlockConstantTerm_eq_iterated F hw,
    GroupSchemeFunctions.normalizedBlockConstantTerm_eq_domain]
  exact ht.symm

end Langlands.Automorphic
