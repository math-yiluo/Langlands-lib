import Langlands.HarmonicAnalysis.Distribution.CompactSubgroup
import Langlands.HarmonicAnalysis.Distribution.HeckeRealization
import Langlands.HarmonicAnalysis.Distribution.RenardConvolutionDensityProof
import Langlands.HarmonicAnalysis.Distribution.RenardHaarDensityProof
import Langlands.HarmonicAnalysis.GroupAction
import Langlands.Representation.Hecke.NormalizedIndicator
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Normalized Haar integration on compact open subgroups

Helper facts for Renard II.3.12: the normalized Haar distribution `e_K` of a
compact open subgroup is the density of the normalized indicator for every
ambient Haar measure, and it is invariant under left and right translation by
`K` and under inversion.
-/

noncomputable section

open MeasureTheory Measure
open scoped ENNReal NNReal

namespace Langlands.HarmonicAnalysis.Distribution.RenardHecke

universe uG uH

section CompactGroup

variable {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]

/-- Mathlib's Haar measure normalized on the whole compact group has mass one. -/
theorem isProbabilityMeasure_haarMeasure_top :
    IsProbabilityMeasure (haarMeasure (⊤ : TopologicalSpace.PositiveCompacts H)) := by
  refine ⟨?_⟩
  have h := haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts H))
  rwa [TopologicalSpace.PositiveCompacts.coe_top] at h

/-- A finite Haar measure on a compact group is right invariant. -/
theorem isMulRightInvariant_of_compact (ν : Measure H) [IsHaarMeasure ν]
    [IsProbabilityMeasure ν] : ν.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h := map_right_mul_eq_modularCharacterFun_smul ν g
  have hΔ : modularCharacterFun g = 1 := by
    have h1 := congrArg (fun μ : Measure H => μ Set.univ) h
    simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul,
      mul_one] at h1
    exact_mod_cast h1.symm
  rw [h, hΔ, one_smul]

/-- A probability Haar measure on a compact group is inversion invariant. -/
theorem isInvInvariant_of_compact (ν : Measure H) [IsHaarMeasure ν]
    [IsProbabilityMeasure ν] : ν.IsInvInvariant := by
  have := isMulRightInvariant_of_compact ν
  have : IsHaarMeasure ν.inv :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  have : IsProbabilityMeasure ν.inv :=
    ⟨by rw [Measure.inv_apply, Set.inv_univ, measure_univ]⟩
  exact ⟨isHaarMeasure_eq_of_isProbabilityMeasure ν.inv ν⟩

end CompactGroup

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Bridge

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- With the subtype Borel structure, a probability Haar measure on a compact
open subgroup is the ambient Haar measure restricted to it and divided by its mass. -/
theorem integral_probabilityHaar_subtype (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hK : IsCompact (K : Set G)) [CompactSpace K] (ν : Measure K) [IsHaarMeasure ν]
    [IsProbabilityMeasure ν] (f : G → ℂ) :
    ∫ k, f k ∂ν = ((μ.real (K : Set G) : ℂ))⁻¹ * ∫ x in (K : Set G), f x ∂μ := by
  have hKm : MeasurableSet (K : Set G) := hKo.measurableSet
  have : (μ.comap K.subtype).IsHaarMeasure :=
    IsHaarMeasure.comap (mH := inferInstance) μ hKo.isOpenEmbedding_subtypeVal
  have hlam := isMulInvariant_eq_smul_of_compactSpace (μ.comap K.subtype) ν
  set c := haarScalarFactor (μ.comap K.subtype) ν with hc_def
  have huniv : (μ.comap K.subtype) Set.univ = μ (K : Set G) := by
    have h := comap_subtype_coe_apply hKm μ (Set.univ : Set (K : Set G))
    rw [Set.image_univ, Subtype.range_coe] at h
    exact h
  have hc : ((c : ℝ≥0∞)) = μ (K : Set G) := by
    rw [← huniv, hlam, Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one]
  have hreal : μ.real (K : Set G) = (c : ℝ) := by
    rw [Measure.real, ← hc, ENNReal.coe_toReal]
  have hpos : (0 : ℝ) < μ.real (K : Set G) :=
    ENNReal.toReal_pos (ne_of_gt (hKo.measure_pos μ ⟨1, K.one_mem⟩)) hK.measure_ne_top
  have hne : ((μ.real (K : Set G) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  rw [← integral_subtype_comap hKm f]
  change ∫ k, f k ∂ν = _ * ∫ x : K, f x ∂(μ.comap K.subtype)
  rw [hlam, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, ← hreal,
    ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- The same formula for any Borel structure on the subgroup. -/
theorem integral_probabilityHaar (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hK : IsCompact (K : Set G)) {m : MeasurableSpace K} [hm : BorelSpace K]
    [CompactSpace K] (ν : Measure K) [IsHaarMeasure ν] [IsProbabilityMeasure ν]
    (f : G → ℂ) :
    ∫ k, f k ∂ν = ((μ.real (K : Set G) : ℂ))⁻¹ * ∫ x in (K : Set G), f x ∂μ := by
  have h2 : (Subtype.instMeasurableSpace : MeasurableSpace K) = borel K :=
    (Subtype.borelSpace (K : Set G)).measurable_eq
  have h : m = Subtype.instMeasurableSpace := hm.measurable_eq.trans h2.symm
  subst h
  exact integral_probabilityHaar_subtype μ K hKo hK ν f

/-- Renard's `e_K`, evaluated through any ambient Haar measure. -/
theorem compactSubgroupHaar_apply_eq [T2Space G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hK : IsCompact (K : Set G)) (f : SchwartzBruhat G) :
    (compactSubgroupHaar K hK : Distribution G) f =
      ((μ.real (K : Set G) : ℂ))⁻¹ * ∫ x in (K : Set G), f x ∂μ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let _ : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  have := isProbabilityMeasure_haarMeasure_top (H := K)
  exact integral_probabilityHaar μ K hKo hK (haarMeasure ⊤) (fun x => f x)

end Bridge

section Invariance

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- Left translation by an element of `K` preserves `e_K`. -/
theorem compactSubgroupHaar_leftTests (K : Subgroup G) (hK : IsCompact (K : Set G))
    {k : G} (hk : k ∈ K) (f : SchwartzBruhat G) :
    (compactSubgroupHaar K hK : Distribution G) (GroupAction.leftTests k f) =
      (compactSubgroupHaar K hK : Distribution G) f := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let _ : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  change ∫ y : K, f (k⁻¹ * y.val) ∂(haarMeasure ⊤) = ∫ y : K, f y.val ∂(haarMeasure ⊤)
  exact integral_mul_left_eq_self (fun y : K => f y.val) (⟨k, hk⟩⁻¹ : K)

/-- Right translation by an element of `K` preserves `e_K`. -/
theorem compactSubgroupHaar_rightTests (K : Subgroup G) (hK : IsCompact (K : Set G))
    {k : G} (hk : k ∈ K) (f : SchwartzBruhat G) :
    (compactSubgroupHaar K hK : Distribution G) (GroupAction.rightTests k f) =
      (compactSubgroupHaar K hK : Distribution G) f := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let _ : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  have := isProbabilityMeasure_haarMeasure_top (H := K)
  have := isMulRightInvariant_of_compact
    (haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K))
  change ∫ y : K, (GroupAction.rightTests k f) y.val ∂(haarMeasure ⊤) =
    ∫ y : K, f y.val ∂(haarMeasure ⊤)
  simp only [GroupAction.rightTests_apply]
  exact integral_mul_right_eq_self (fun y : K => f y.val) (⟨k, hk⟩ : K)

/-- Inversion preserves `e_K`. -/
theorem compactSubgroupHaar_inversionTests (K : Subgroup G) (hK : IsCompact (K : Set G))
    (f : SchwartzBruhat G) :
    (compactSubgroupHaar K hK : Distribution G) (GroupAction.inversionTests f) =
      (compactSubgroupHaar K hK : Distribution G) f := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let _ : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  have := isProbabilityMeasure_haarMeasure_top (H := K)
  have := isInvInvariant_of_compact
    (haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K))
  change ∫ y : K, f (y.val)⁻¹ ∂(haarMeasure ⊤) = ∫ y : K, f y.val ∂(haarMeasure ⊤)
  exact integral_inv_eq_self (fun y : K => f y.val) _

theorem leftDistributions_compactSubgroupHaar (K : Subgroup G) (hK : IsCompact (K : Set G))
    {k : G} (hk : k ∈ K) :
    GroupAction.leftDistributions k (compactSubgroupHaar K hK : Distribution G) =
      compactSubgroupHaar K hK := by
  ext f
  rw [GroupAction.leftDistributions_apply]
  exact compactSubgroupHaar_leftTests K hK (K.inv_mem hk) f

theorem rightDistributions_compactSubgroupHaar (K : Subgroup G) (hK : IsCompact (K : Set G))
    {k : G} (hk : k ∈ K) :
    GroupAction.rightDistributions k (compactSubgroupHaar K hK : Distribution G) =
      compactSubgroupHaar K hK := by
  ext f
  rw [GroupAction.rightDistributions_apply]
  exact compactSubgroupHaar_rightTests K hK (K.inv_mem hk) f

theorem inversionDistributions_compactSubgroupHaar (K : Subgroup G)
    (hK : IsCompact (K : Set G)) :
    GroupAction.inversionDistributions (compactSubgroupHaar K hK : Distribution G) =
      compactSubgroupHaar K hK := by
  ext f
  rw [GroupAction.inversionDistributions_apply]
  exact compactSubgroupHaar_inversionTests K hK f

/-- `e_K` is supported in `K`. -/
theorem support_compactSubgroupHaar_subset (K : Subgroup G) (hK : IsCompact (K : Set G)) :
    support (compactSubgroupHaar K hK : Distribution G) ⊆ K :=
  support_subset_of_mem_supportedOn hK.isClosed
    (compactSubgroupDistribution_mem_supportedOn K hK)

/-- `e_K` has total mass one: it takes the value `c` on tests equal to `c` on `K`. -/
theorem compactSubgroupHaar_eq_of_const (K : Subgroup G) (hK : IsCompact (K : Set G))
    (f : SchwartzBruhat G) {c : ℂ} (hf : ∀ k ∈ K, f k = c) :
    (compactSubgroupHaar K hK : Distribution G) f = c := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let _ : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  have := isProbabilityMeasure_haarMeasure_top (H := K)
  change ∫ y : K, f y.val ∂(haarMeasure ⊤) = c
  calc
    (∫ y : K, f y.val ∂(haarMeasure ⊤)) = ∫ _y : K, c ∂(haarMeasure ⊤) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => hf y.val y.property)
    _ = c := by simp

/-- The extended pairing of `e_K` with a function constant on `K`. -/
theorem compactSupportPairing_compactSubgroupHaar_of_const (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (φ : LocallyConstant G ℂ) {c : ℂ}
    (hφ : ∀ k ∈ K, φ k = c) :
    compactSupportPairing (compactSubgroupHaar K hK) φ = c := by
  obtain ⟨ψ, hψ⟩ := exists_testFunction_agrees_on_compact hK φ
  rw [compactSupportPairing_eq_of_agrees _ φ ψ
    (fun x hx => hψ x (support_compactSubgroupHaar_subset K hK hx))]
  exact compactSubgroupHaar_eq_of_const K hK ψ (fun k hk => (hψ k hk).trans (hφ k hk))

/-- `e_K` is a left unit for left-`K`-invariant compact distributions. -/
theorem convolution_compactSubgroupHaar_left (K : Subgroup G) (hK : IsCompact (K : Set G))
    (D : compactlySupported (X := G))
    (hD : ∀ k ∈ K, GroupAction.leftDistributions k (D : Distribution G) = D) :
    convolution (compactSubgroupHaar K hK) D = D := by
  apply Subtype.ext
  ext f
  rw [convolution_eq_pairing]
  apply compactSupportPairing_compactSubgroupHaar_of_const
  intro k hk
  rw [compactPartial_apply, compactSupportPairing_eq_of_agrees D _
    (GroupAction.leftTests k⁻¹ f) (fun y _ => by
      change (GroupAction.leftTests k⁻¹ f) y = f (k * y)
      simp)]
  rw [← GroupAction.leftDistributions_apply, hD k hk]

/-- `e_K` is a right unit for right-`K`-invariant compact distributions. -/
theorem convolution_compactSubgroupHaar_right (K : Subgroup G) (hK : IsCompact (K : Set G))
    (D : compactlySupported (X := G))
    (hD : ∀ k ∈ K, GroupAction.rightDistributions k (D : Distribution G) = D) :
    convolution D (compactSubgroupHaar K hK) = D := by
  apply Subtype.ext
  ext f
  rw [convolution_eq_pairing, compactPairing_swap]
  apply compactSupportPairing_compactSubgroupHaar_of_const
  intro k hk
  rw [compactPartial_apply, compactSupportPairing_eq_of_agrees D _
    (GroupAction.rightTests k f) (fun y _ => by
      change (GroupAction.rightTests k f) y = f (y * k)
      simp)]
  have h := congrArg (fun E : Distribution G => E f) (hD k⁻¹ (K.inv_mem hk))
  simp only [GroupAction.rightDistributions_apply, inv_inv] at h
  exact h

/-- Right invariance of the second factor passes to a convolution. -/
theorem rightDistributions_convolution (T S : compactlySupported (X := G)) (g : G)
    (hS : GroupAction.rightDistributions g (S : Distribution G) = S) :
    GroupAction.rightDistributions g (convolution T S : Distribution G) = convolution T S := by
  have hS' : convolution S (compactDirac g⁻¹) = S := Subtype.ext (by
    rw [convolution_dirac_right, inv_inv]
    exact hS)
  have h := convolution_dirac_right g⁻¹ (convolution T S)
  rw [inv_inv, convolution_associative, hS'] at h
  exact h.symm

/-- Left invariance of the first factor passes to a convolution. -/
theorem leftDistributions_convolution (T S : compactlySupported (X := G)) (g : G)
    (hT : GroupAction.leftDistributions g (T : Distribution G) = T) :
    GroupAction.leftDistributions g (convolution T S : Distribution G) = convolution T S := by
  have hT' : convolution (compactDirac g) T = T :=
    Subtype.ext ((convolution_dirac_left g T).trans hT)
  have h := convolution_dirac_left g (convolution T S)
  rw [← convolution_associative, hT'] at h
  exact h.symm

end Invariance

section Density

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

omit [IsTopologicalGroup G] in
/-- The Haar density map on scalar tests is injective. -/
theorem testDensity_injective : Function.Injective (testDensity μ) := by
  intro f g hfg
  have h : (⟨(f : G → ℂ), f.locallyConstant⟩ : LocallyConstant G ℂ) =
      ⟨(g : G → ℂ), g.locallyConstant⟩ :=
    RenardHaar.density_injective μ hfg
  ext x
  exact congrArg (fun q : LocallyConstant G ℂ => q x) h

/-- The density of the normalized indicator is `e_K`. -/
theorem heckeDistribution_normalizedIndicator (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) :
    heckeDistribution μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) =
      (compactSubgroupHaar K.toSubgroup hK : Distribution G) := by
  ext f
  rw [heckeDistribution_apply, compactSubgroupHaar_apply_eq μ K.toSubgroup K.isOpen hK f]
  simp only [Hecke.HeckeAlgebra.normalizedIndicator_apply, OpenSubgroup.coe_toSubgroup]
  rw [← integral_const_mul, ← integral_indicator K.isOpen.measurableSet]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  by_cases hx : x ∈ K <;> simp [hx]

theorem compactTestDensity_normalizedIndicator (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) :
    compactTestDensity μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) =
      compactSubgroupHaar K.toSubgroup hK :=
  Subtype.ext (heckeDistribution_normalizedIndicator μ K hK)

/-- Convolution of Haar densities is the density of the Hecke product. -/
theorem convolution_compactTestDensity (f g : SchwartzBruhat G) :
    convolution (compactTestDensity μ f) (compactTestDensity μ g) =
      compactTestDensity μ (Hecke.TestFunction.convolution μ f g) := by
  obtain ⟨F, H, hF, hH, hFH⟩ := RenardConvolution.heckeCompatibility G μ f g
  have hF' : F = compactTestDensity μ f := Subtype.ext hF
  have hH' : H = compactTestDensity μ g := Subtype.ext hH
  subst hF' hH'
  exact Subtype.ext hFH

/-- A Dirac mass acts on a Haar density by left translation of the density. -/
theorem convolution_compactDirac_compactTestDensity (g : G) (f : SchwartzBruhat G) :
    convolution (compactDirac g) (compactTestDensity μ f) =
      compactTestDensity μ (GroupAction.leftTests g f) := by
  apply Subtype.ext
  rw [convolution_testDensity_left]
  change testDensity μ _ = testDensity μ _
  congr 1
  ext x
  change (Hecke.TestFunction.leftTranslate x (Hecke.TestFunction.inversion f)) g =
    f (g⁻¹ * x)
  simp

end Density

end Langlands.HarmonicAnalysis.Distribution.RenardHecke
