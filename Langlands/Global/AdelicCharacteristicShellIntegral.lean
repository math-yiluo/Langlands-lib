import Langlands.Global.AdelicCharacteristicShellCoordinates
import Langlands.Global.AdelicRelativeSplitIntegral
import Langlands.Global.InducedInnerProductSesquilinearProof

/-! # The characteristic shell integral on the rational parabolic quotient -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set Topology
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints PositiveRealTorus
  AdelicSiegelFactors ArthurTruncation ArthurParabolicSpaces AdelicGroupPoints.ParabolicIwasawaMeasure

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p fam.bot) K)

local notation "M" => fam.M J
local notation "P" => fam.P J
local notation "A" => fam.A J
local notation "T" => fam.T
local notation "D" => fam.coroots
local notation "p" => fam.p J
local notation "u" => fam.iU J
local notation "l" => fam.l J
local notation "a" => fam.a J
local notation "j" => fam.l J ≫ fam.p J
local notation "B" => relativePositiveSubgroup (fam.l J ≫ fam.p J) (fam.a J)
local notation "N" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (fam.iU J ≫ fam.p J))
local notation "ΓN" =>
  AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (fam.iU J ≫ fam.p J))
local notation "M₁" => normOneSubgroup F M
local notation "ΓM" => rationalNormOneSubgroup F M
local notation "ΓP" => parabolicRationalNormOneSubgroup (F := F) (fam.p J)
local notation "Γstd" =>
  parabolicRationalNormOneSubgroup (F := F) (Standard.parabolicHom fam.i fam.ν J.val)
local notation "dN" =>
  AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range (fam.iU J ≫ fam.p J))
local notation "DN" => LeftCosetSpace.fundamentalDomain ΓN dN
local notation "DM" => LeftCosetSpace.fundamentalDomain ΓM (isDiscrete_rationalNormOneSubgroup F M)
local notation "Q" => LeftCosetSpace ΓP
local notation "ψ" => fam.characteristicShellCoordinates J hK
local notation "dP" => LeftCosetSpace.haarQuotientMeasure ΓP (isDiscrete_parabolicRationalNormOneSubgroup p)
local notation "KM" => K.comap (ContinuousMonoidHom.toMonoidHom (map F M G (fam.l J ≫ fam.p J)))
local notation "Δ" => simpleRelativeRoots fam.i fam.ν
local notation "δ" => relativePositiveDensity p l a
local notation "qM" => LeftCosetSpace.mk ΓM
local notation "H₀" => fam.minimalHeight hK
local notation "hU" => fam.isUnipotentRadical J
set_option quotPrecheck false in
local notation "hM" => (fam.isCompatible J).levi.isConnectedReductive
set_option quotPrecheck false in
local notation "ha" => (fam.isCompatible J).splitComponent

local instance : IsAffineHom (M).X.hom := (hM).isAffineHom
local instance : IsClosedImmersion (p).hom.hom.left := fam.isClosedImmersion_p J
local instance : IsClosedImmersion (u ≫ p).hom.hom.left := fam.closedU J
local instance : IsIso (subgroupMultiplication l u) :=
  Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication
    (⟨⟨T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩ : ParabolicRootPresentation p l a)
    fam.connectedReductive hU

local instance radical_isClosed : IsClosed (N : Set (AdelicGroupPoints F G)) :=
  AdelicSubgroupPoints.isClosed_adelicPoints_range F G (u ≫ p)

local instance : LocallyCompactSpace N :=
  (radical_isClosed fam J).locallyCompactSpace

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem mem_parabolicRationalNormOne_iff {P' : GroupScheme (Spec (CommRingCat.of F))}
    (f : P' ⟶ G) (g : normOneSubgroup F G) :
    g ∈ parabolicRationalNormOneSubgroup f ↔ g.val ∈ rationalImage F f := by
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨q, rfl⟩
  · rintro ⟨q, hq⟩
    exact ⟨rationalNormOne F P' q, ⟨q, rfl⟩, Subtype.ext hq⟩

variable (C : CompactFactors F G (Standard.unipotentScheme fam.i fam.ν ∅)
  (Standard.leviScheme fam.i fam.ν ∅))

private theorem measurableSet_shellLift (T₀ Tp S : V T) :
    MeasurableSet (fam.presentedCharacteristicShellLift J hK C T₀ Tp S) := by
  have h := (fam.isCompatible J).parabolic_eq.trans
    (Standard.isRepresentedBy_parabolicHom fam.i fam.ν J.val).2.symm
  have hr := le_antisymm (rationalImage_le_of_range_le _ _ h.le)
    (rationalImage_le_of_range_le _ _ h.ge)
  have hΓ : ΓP = Γstd := by
    ext g
    rw [mem_parabolicRationalNormOne_iff, mem_parabolicRationalNormOne_iff, hr]
  change MeasurableSet (LeftCosetSpace.mk ΓP '' fam.characteristicShellPoints J hK C T₀ Tp S)
  rw [hΓ]
  exact measurableSet_characteristicShellLift fam.connectedReductive fam.maximalSplit D
    (fam.isIwasawaCompact_standardBot hK) fam.bijective_restrictToTorus_bot C J T₀ Tp S

set_option maxHeartbeats 1000000 in
/-- The product measure maps to the restricted rational parabolic quotient. -/
theorem characteristicRelativeProductMeasure_preserving_lift
    (hKM : IsMaximalCompactSubgroup F M KM) (hcov : IsRationalCovering C)
    (dn : Measure N) [dn.IsHaarMeasure] :
    ∃ da : Measure B, da.IsHaarMeasure ∧ SigmaFinite da ∧
      ∀ T₀ Tp S : V T, (∀ α ∈ Δ, 0 ≤ eval T α (Tp - T₀)) →
        (∀ α ∈ J.val, 0 ≤ eval T α S) →
        MeasurePreserving ψ
          (fam.characteristicRelativeProductMeasure J hK dn da T₀ Tp S)
          ((dP).restrict (fam.presentedCharacteristicShellLift J hK C T₀ Tp S)) := by
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G fam.connectedReductive T fam.i
    fam.maximalSplit fam.ν fam.generic J.val J.property
  let χ := CommGroupScheme.groupHom ζ ≫ fam.i
  have hP : (Dynamic.parabolic χ).IsRepresentedBy p := by
    rw [← (hcompare ζ hζ).1, ← (fam.isCompatible J).parabolic_eq]
    exact (fam.isCompatible J).parabolic.isClosedSubgroup.isRepresentedBy_range
  have hR : (Dynamic.unipotent χ).IsRepresentedBy (u ≫ p) := by
    rw [← (hcompare ζ hζ).2.2, ← fam.range_radical_eq_standardUnipotent J]
    exact (IsClosedSubgroup.isRepresentedBy_range (fam.closedU J))
  obtain ⟨da, hda, hsf, hmap⟩ := relativeParabolicQuotientMeasure p u l hU a hM ha
    fam.connectedReductive hP hR (fam.isIwasawaCompact_index hK J) dn
  refine ⟨da, hda, hsf, fun T₀ Tp S hcut hS => ?_⟩
  have hψ : MeasurePreserving ψ (fam.characteristicShellCoordinateMeasure J hK dn da) dP :=
    ⟨measurable_normOneRelativeParabolicQuotientCoordinates p u l hU a hM ha hK.isCompact,
      hmap.symm⟩
  have hm := hψ.restrict_preimage (fam.measurableSet_shellLift J hK C T₀ Tp S)
  have hpre : ψ ⁻¹' fam.presentedCharacteristicShellLift J hK C T₀ Tp S =
      (Set.univ ×ˢ (fam.characteristicSplitHeightRegion J hK Tp S ×ˢ
        (qM ⁻¹' fam.characteristicLeviHeightRegion J hK T₀ Tp))) ×ˢ Set.univ := by
    rw [fam.characteristicShellRelativeProduct J hK C hKM hcov T₀ Tp S hcut hS]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and, and_true, Set.mem_preimage]
  rw [hpre, characteristicShellCoordinateMeasure, ← Measure.prod_restrict, ← Measure.prod_restrict,
    ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_univ] at hm
  exact hm

private theorem continuous_leviHeightFunctional (g : V T →ₗ[ℝ] ℝ) :
    Continuous (fun m : M₁ => g (H₀ (map F M G (j) m.val))) := by
  obtain ⟨ζ, hζ⟩ := (isPerfPair_of_isSplitTorus fam.maximalSplit.isSplitSubtorus.1).bijective_left.surjective g
  obtain ⟨t₀, ht₀⟩ := fam.bijective_restrictToTorus_bot.surjective ζ
  rw [← hζ, ← ht₀]
  change Continuous (fun m : M₁ => pair T (restrictToTorus F fam.i fam.ν ∅ t₀)
    (height fam.maximalSplit (fam.isIwasawaCompact_standardBot hK)
      fam.bijective_restrictToTorus_bot (map F M G (j) m.val)))
  simp_rw [height, pair_toA0]
  exact (InducedInnerProductSesquilinear.continuous_realParameterPairing F _ t₀).comp
    ((fam.isIwasawaCompact_standardBot hK).continuous_height.comp
      ((map F M G (j)).continuous.comp continuous_subtype_val))

/-- The Levi quotient height region is Borel. The height conditions are half-spaces
in the Levi coroot span, which already contains the height of every norm-one point. -/
theorem measurableSet_characteristicLeviHeightRegion (T₀ Tp : V T) :
    MeasurableSet (fam.characteristicLeviHeightRegion J hK T₀ Tp) := by
  let : Countable ΓM := LeftCosetSpace.countable_of_isDiscrete ΓM (isDiscrete_rationalNormOneSubgroup F M)
  apply LeftCosetSpace.measurableSet_image_mk
  let proj := ArthurRelative.levelProjection fam.connectedReductive fam.maximalSplit fam.ν D J.val
  let H (m : M₁) := H₀ (map F M G (j) m.val)
  let w := ArthurRelative.weight fam.connectedReductive fam.maximalSplit fam.ν D J.val
  have hEq : {m : M₁ | H m ∈ characteristicLeviChamber fam.connectedReductive fam.maximalSplit D J T₀ Tp} =
      ⋂ α : J.val, {m : M₁ | eval T α.val (T₀ - proj T₀) ≤ eval T α.val (H m) ∧
        w α.val (H m) ≤ w α.val (Tp - proj Tp)} := by
    ext m
    change (H m ∈ _ ∧ _) ↔ _
    rw [and_iff_right (fam.minimalHeight_normOneLevi_mem J hK m), Set.mem_iInter]
    simp only [Set.mem_ofPred_eq, map_sub, sub_nonneg, sub_nonpos]
    exact ⟨fun h α => h α.val α.property, fun h α hα => h ⟨α, hα⟩⟩
  rw [hEq]
  let : Finite J.val :=
    ((fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i fam.ν).subset J.property).to_subtype
  apply MeasurableSet.iInter
  intro α
  exact ((isClosed_le continuous_const (fam.continuous_leviHeightFunctional J hK (eval T α.val))).inter
    (isClosed_le (fam.continuous_leviHeightFunctional J hK (w α.val)) continuous_const)).measurableSet

private theorem characteristicShellCoordinates_left_rationalLevi (b : B) (k : K) (r : ΓM) (m : M₁) :
    ψ ((1, (b, r.val * m)), k) = ψ ((1, (b, m)), k) := by
  obtain ⟨s, hs⟩ := r.property
  change rationalNormOne F M s = r.val at hs
  let sP : RationalGroupPoints F P := (M).affinePointsTarget l _ s
  let ds := mapNormOne F P G p (rationalNormOne F P sP)
  have hds : ds ∈ ΓP := ⟨_, ⟨sP, rfl⟩, rfl⟩
  have hδ : ds.val = map F M G (j) r.val.val := by
    rw [← hs]
    change map F P G p (rational F P sP) = _
    rw [← map_rational l s, ← map_comp_apply_of_hom]
    rfl
  have hc : Commute (fam.relativeSplitPoint J b) ds.val := by
    rw [hδ, relativeSplitPoint]
    exact (positivePointMap_commute F M A a (ha).1.2 b.val r.val.val).map (map F M G (j))
  rw [fam.characteristicShellCoordinates_eq_mk J hK, fam.characteristicShellCoordinates_eq_mk J hK]
  have he : fam.characteristicShellRepresentative J hK ((1, (b, r.val * m)), k) =
      ds * fam.characteristicShellRepresentative J hK ((1, (b, m)), k) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, fam.characteristicShellRepresentative_val J hK,
      fam.characteristicShellRepresentative_val J hK]
    simp only [OneMemClass.coe_one, one_mul, Subgroup.coe_mul, map_mul]
    rw [← hδ, ← mul_assoc (fam.relativeSplitPoint J b) ds.val, hc.eq]
    group
  rw [he]
  exact LeftCosetSpace.mk_subgroup_mul ΓP ⟨ds, hds⟩ _

/-- Insert a split point and a compact point on either side of the Levi representative. -/
def characteristicShellLeviCoordinates (b : B) (k : K) : NormOneRationalQuotient F M → Q :=
  LeftCosetSpace.lift ΓM (fun m => ψ ((1, (b, m)), k))
    (fam.characteristicShellCoordinates_left_rationalLevi J hK b k)

@[simp]
theorem characteristicShellLeviCoordinates_mk (b : B) (k : K) (m : M₁) :
    fam.characteristicShellLeviCoordinates J hK b k (qM m) = ψ ((1, (b, m)), k) := rfl

theorem measurable_characteristicShellLeviCoordinates (b : B) (k : K) :
    Measurable (fam.characteristicShellLeviCoordinates J hK b k) := by
  intro s hs
  rw [measurableSet_quotient, Quotient.mk''_eq_mk]
  change MeasurableSet ((fun m : M₁ => ψ ((1, (b, m)), k)) ⁻¹' s)
  have hψ : Measurable ψ :=
    measurable_normOneRelativeParabolicQuotientCoordinates p u l hU a hM ha hK.isCompact
  exact (hψ.comp ((measurable_const.prodMk (measurable_const.prodMk measurable_id)).prodMk
    measurable_const)) hs

include fam J in
/-- The compact radical quotient allows Haar with mass one on its fundamental domain. -/
theorem exists_normalized_shell_radicalHaar :
    ∃ dn : Measure N, dn.IsHaarMeasure ∧ dn DN = 1 := by
  let R := SubgroupFunctor.range (u ≫ p)
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G R) := fam.compactSpace_radicalRationalQuotient J
  let : IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure ΓN dN) :=
    AdelicSubgroupPoints.rationalQuotientHaarMeasure_isFiniteMeasure F G R
  have h₀ := LeftCosetSpace.haar_fundamentalDomain_ne_zero ΓN dN
  have htop := LeftCosetSpace.haar_fundamentalDomain_ne_top ΓN dN
  let dn := ((Measure.haar : Measure N) DN)⁻¹ • (Measure.haar : Measure N)
  refine ⟨dn, Measure.IsHaarMeasure.smul (Measure.haar : Measure N)
    (ENNReal.inv_ne_zero.mpr htop) (ENNReal.inv_ne_top.mpr h₀), ?_⟩
  change ((((Measure.haar : Measure N) DN)⁻¹ • (Measure.haar : Measure N)) : Measure N) DN = 1
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h₀ htop]

local notation "dk" => compactHaarProbability F G K hK.isCompact
local notation "dM" => normOneRationalQuotientHaarMeasure F M
local notation "sq" => fun b : B => fam.halfModulus J (fam.relativeParabolicSplitPoint J b) ^ 2

/-- The product of two half-modulus normalizations in the shell slice. -/
def normalizedCharacteristicShellLeviFunction (f : Q → ℂ) (b : B) (k : K)
    (m : NormOneRationalQuotient F M) : ℂ :=
  (sq b)⁻¹ * f (fam.characteristicShellLeviCoordinates J hK b k m)

/-- A radical-invariant integrand on the lifted shell is integrated over the split,
intrinsic norm-one Levi quotient and compact factors, after canceling the density. -/
def CharacteristicShellIntegralStatement : Prop :=
  IsMaximalCompactSubgroup F M KM → IsRationalCovering C →
    ∃ da : Measure B, da.IsHaarMeasure ∧ SigmaFinite da ∧
      ∀ T₀ Tp S : V T, (∀ α ∈ Δ, 0 ≤ eval T α (Tp - T₀)) →
        (∀ α ∈ J.val, 0 ≤ eval T α S) →
        ∀ f : Q → ℂ, Measurable f →
          IntegrableOn f (fam.presentedCharacteristicShellLift J hK C T₀ Tp S) dP →
          (∀ (n : N) (b : B) (m : M₁) (k : K),
            f (ψ ((n, (b, m)), k)) = f (ψ ((1, (b, m)), k))) →
          (∫ q in fam.presentedCharacteristicShellLift J hK C T₀ Tp S, f q ∂dP) =
            ∫ k, ∫ b in fam.characteristicSplitHeightRegion J hK Tp S,
              ∫ m in fam.characteristicLeviHeightRegion J hK T₀ Tp,
                fam.normalizedCharacteristicShellLeviFunction J hK f b k m ∂dM ∂da ∂dk

set_option maxHeartbeats 1400000 in
/-- Fubini on the exact product coordinates gives the Levi slices. The radical
fundamental domain has mass one and the square of the half-modulus cancels the split density. -/
theorem characteristicShellIntegral : fam.CharacteristicShellIntegralStatement J hK C := by
  intro hKM hcov
  obtain ⟨dn, hdn, hm₁⟩ := fam.exists_normalized_shell_radicalHaar J
  let : dn.IsHaarMeasure := hdn
  obtain ⟨da, hda, hsf, h⟩ :=
    fam.characteristicRelativeProductMeasure_preserving_lift J hK C hKM hcov dn
  let : SigmaFinite da := hsf
  refine ⟨da, hda, hsf, fun T₀ Tp S hcut hS f hf hI hinv => ?_⟩
  let L := fam.characteristicLeviHeightRegion J hK T₀ Tp
  let X := fam.characteristicSplitHeightRegion J hK Tp S
  let dn' := dn.restrict DN
  let dm' := ((Measure.haar : Measure M₁).restrict DM).restrict (qM ⁻¹' L)
  let da' := (da.withDensity δ).restrict X
  let F' (k : K) (b : B) (m : M₁) := f (ψ ((1, (b, m)), k))
  have h₁ : dn' univ = 1 := (Measure.restrict_apply_univ _).trans hm₁
  have hquot : MeasurePreserving qM dm' ((dM).restrict L) :=
    (LeftCosetSpace.measurePreserving_mk ΓM Measure.haar DM).restrict_preimage
      (fam.measurableSet_characteristicLeviHeightRegion J hK T₀ Tp)
  have hψ := h T₀ Tp S hcut hS
  have hI' : Integrable (f ∘ ψ) ((dn'.prod (da'.prod dm')).prod dk) :=
    hψ.integrable_comp_of_integrable hI
  change Integrable f ((dP).restrict (fam.presentedCharacteristicShellLift J hK C T₀ Tp S)) at hI
  rw [← hψ.map_eq] at hI
  change (∫ q, f q ∂((dP).restrict (fam.presentedCharacteristicShellLift J hK C T₀ Tp S))) = _
  rw [← hψ.map_eq, integral_map hψ.measurable.aemeasurable hI.aestronglyMeasurable]
  change (∫ x, (f ∘ ψ) x ∂((dn'.prod (da'.prod dm')).prod dk)) = _
  rw [integral_prod_symm _ hI']
  apply integral_congr_ae
  filter_upwards [hI'.prod_left_ae] with k hk
  rw [integral_prod_symm _ hk]
  have hconst (b : B) (m : M₁) :
      (∫ n, f (ψ ((n, (b, m)), k)) ∂dn') = F' k b m := by
    simp only [hinv, integral_const, measureReal_def, h₁, ENNReal.toReal_one, one_smul, F']
  have hF : Integrable (fun y : B × M₁ => F' k y.1 y.2) (da'.prod dm') :=
    hk.integral_prod_right.congr (Filter.Eventually.of_forall fun y => hconst y.1 y.2)
  change (∫ y : B × M₁, ∫ n, f (ψ ((n, (y.1, y.2)), k)) ∂dn' ∂(da'.prod dm')) = _
  simp_rw [hconst]
  rw [integral_prod _ hF]
  have hslice (b : B) :
      (∫ m, F' k b m ∂dm') =
        ∫ q in L, f (fam.characteristicShellLeviCoordinates J hK b k q) ∂dM := by
    have hmeas : AEStronglyMeasurable (f ∘ fam.characteristicShellLeviCoordinates J hK b k)
        (Measure.map qM dm') :=
      (hf.comp (fam.measurable_characteristicShellLeviCoordinates J hK b k)).aestronglyMeasurable
    simpa only [hquot.map_eq, Function.comp_def, characteristicShellLeviCoordinates_mk, F'] using
      (integral_map hquot.measurable.aemeasurable hmeas).symm
  simp_rw [hslice]
  rw [← fam.integral_relativePositiveDensity_cancel J da X
    (fun b => ∫ q in L, fam.normalizedCharacteristicShellLeviFunction J hK f b k q ∂dM)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun b => by
    have hs : sq b ≠ 0 := pow_ne_zero _ (parameterPower_ne_zero _ _)
    simp only [normalizedCharacteristicShellLeviFunction, integral_const_mul, ← mul_assoc,
      mul_inv_cancel₀ hs, one_mul]

end Langlands.Global.StandardParabolicFamily
