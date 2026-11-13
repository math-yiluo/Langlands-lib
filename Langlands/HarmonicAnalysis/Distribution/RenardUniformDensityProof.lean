import Langlands.HarmonicAnalysis.Distribution.RenardUniformDensityStatements
import Langlands.HarmonicAnalysis.Distribution.RenardConvolutionProof
import Langlands.HarmonicAnalysis.Distribution.RenardHaarDensityProof
import Langlands.HarmonicAnalysis.Distribution.RenardModularProof
import Langlands.Representation.Hecke.CommonInvarianceProof
import Langlands.Representation.Hecke.NormalizedIndicator

/-! # Renard II.3.12: proof of the uniform density range and discrete criteria -/

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Langlands.HarmonicAnalysis.Distribution.RenardUniformDensity

universe uG

open GroupFunctionSpaces

section Inversion

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- Inversion of a distribution supported on `Z` is supported on `Z⁻¹`. -/
theorem inversion_mem_compactlySupported {D : Distribution G}
    (hD : D ∈ compactlySupported) :
    GroupAction.inversionDistributions D ∈ compactlySupported := by
  obtain ⟨Z, hZ, hDZ⟩ := (mem_compactlySupported_iff_exists_compact D).mp hD
  refine (mem_compactlySupported_iff_exists_compact _).mpr ⟨Z⁻¹, hZ.inv, ?_⟩
  intro φ hφ
  change D (GroupAction.inversionTests φ) = 0
  apply hDZ
  intro z hz
  change φ z⁻¹ = 0
  exact hφ z⁻¹ (by simpa using hz)

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem inversion_mem_distributionsRight {K : Subgroup G} {D : Distribution G}
    (hD : D ∈ distributionsLeft K) :
    GroupAction.inversionDistributions D ∈ distributionsRight K := by
  rw [mem_fixed_iff]
  intro k
  rw [← GroupAction.inversionDistributions_leftDistributions, (mem_fixed_iff _ _ _).mp hD k]

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem inversion_mem_distributionsLeft {K : Subgroup G} {D : Distribution G}
    (hD : D ∈ distributionsRight K) :
    GroupAction.inversionDistributions D ∈ distributionsLeft K := by
  rw [mem_fixed_iff]
  intro k
  rw [← GroupAction.inversionDistributions_rightDistributions, (mem_fixed_iff _ _ _).mp hD k]

omit [Group G] [IsTopologicalGroup G] in
/-- Distinct points are separated by a compact clopen characteristic function. -/
theorem exists_test_separating {x y : G} (hxy : x ≠ y) :
    ∃ φ : SchwartzBruhat G, φ x ≠ φ y := by
  classical
  obtain ⟨C, hCc, hCn⟩ := exists_compact_mem_nhds x
  obtain ⟨V, hVcl, hxV, hVsub⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.mp
      (Filter.inter_mem (isOpen_compl_singleton.mem_nhds hxy) hCn)
  have hVc : IsCompact V :=
    hCc.of_isClosed_subset hVcl.isClosed (fun z hz => (hVsub hz).2)
  refine ⟨Hecke.TestFunction.characteristic hVcl hVc, ?_⟩
  have hyV : y ∉ V := fun hy => (hVsub hy).1 (Set.mem_singleton y)
  simp [Hecke.TestFunction.characteristic_apply, hxV, hyV]

end Inversion

section Measure

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

omit [IsTopologicalGroup G] in
theorem testDensity_injective : Function.Injective (testDensity μ) := by
  intro f g h
  have h' : (⟨(f : G → ℂ), f.locallyConstant⟩ : LocallyConstant G ℂ) =
      ⟨(g : G → ℂ), g.locallyConstant⟩ := RenardHaar.density_injective μ h
  ext x
  exact congrArg (fun F : LocallyConstant G ℂ => F x) h'

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- Left invariance of a test function passes to its left-Haar density. -/
theorem testDensity_mem_distributionsLeft {K : Subgroup G} {f : SchwartzBruhat G}
    (hf : ∀ k : K, ∀ x, f ((k : G) * x) = f x) :
    testDensity μ f ∈ distributionsLeft K := by
  rw [mem_fixed_iff]
  intro k
  ext φ
  rw [GroupAction.leftDistributions_apply, testDensity_apply, testDensity_apply]
  simp only [GroupAction.leftTests_apply, inv_inv]
  have h := integral_mul_left_eq_self (μ := μ) (fun x => f ((k : G)⁻¹ * x) * φ x) (k : G)
  simp only [inv_mul_cancel_left] at h
  rw [h]
  congr 1
  funext x
  have hk := hf k⁻¹ x
  simp only [InvMemClass.coe_inv] at hk
  rw [hk]

/-- The inversion formula with the reciprocal modular weight. -/
theorem inversion_testDensity (f : SchwartzBruhat G) :
    ∃ g : SchwartzBruhat G,
      (∀ x : G, g x = (((renardModular x : ℝ)⁻¹) : ℂ) * f x⁻¹) ∧
      GroupAction.inversionDistributions (testDensity μ f) = testDensity μ g := by
  obtain ⟨d, hd, -, hinv⟩ := RenardModular.inversionDensity G μ
  refine ⟨multiplyTest d (Hecke.TestFunction.inversion f), fun x => by
    rw [multiplyTest_apply, hd, Hecke.TestFunction.inversion_apply], ?_⟩
  ext φ
  have h := LinearMap.congr_fun hinv
    (multiplyTest ⟨(Hecke.TestFunction.inversion f : G → ℂ),
      (Hecke.TestFunction.inversion f).locallyConstant⟩ φ)
  rw [GroupAction.inversionDistributions_apply, ofMeasure_apply, density_apply] at h
  rw [GroupAction.inversionDistributions_apply, testDensity_apply, testDensity_apply]
  simp only [GroupAction.inversionTests_apply, multiplyTest_apply,
    inv_inv, LocallyConstant.coe_mk] at h ⊢
  rw [h]
  congr 1
  funext x
  ring

/-- Every test density lies in a two-sided compact-invariance level. -/
theorem testDensity_mem_compactDistributionsBoth (f : SchwartzBruhat G) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      testDensity μ f ∈ compactDistributionsBoth K.toSubgroup := by
  classical
  obtain ⟨g, -, hg⟩ := inversion_testDensity μ f
  obtain ⟨K, -, hK, hfg⟩ :=
    Hecke.TestFunction.commonCompactOpenBiInvariance G {f, g} ⊤
  have hf := hfg f (by simp)
  have hg' := hfg g (by simp)
  refine ⟨K, hK, ?_⟩
  rw [compactDistributionsBoth, Submodule.mem_inf, distributionsBoth, Submodule.mem_inf]
  refine ⟨RenardHaar.testDensity_compactlySupported μ f,
    testDensity_mem_distributionsLeft μ hf.1, ?_⟩
  have hgr := inversion_mem_distributionsRight (testDensity_mem_distributionsLeft μ hg'.1)
  rwa [← hg, GroupAction.inversionDistributions_inversionDistributions] at hgr

/-- A compact distribution right invariant under a compact open subgroup is the
density of its convolution with the normalized indicator. -/
theorem mem_range_of_right {K : OpenSubgroup G} (hK : IsCompact (K : Set G))
    {D : Distribution G} (hD : D ∈ compactDistributionsRight K.toSubgroup) :
    D ∈ LinearMap.range (testDensity μ) := by
  rw [compactDistributionsRight, Submodule.mem_inf] at hD
  obtain ⟨hDc, hDr⟩ := hD
  let T : compactlySupported (X := G) := ⟨D, hDc⟩
  let e : SchwartzBruhat G := Hecke.HeckeAlgebra.normalizedIndicator μ K hK
  have he : ∀ y, e y = (μ.real (K : Set G) : ℂ)⁻¹ *
      (K : Set G).indicator (fun _ => (1 : ℂ)) y :=
    Hecke.HeckeAlgebra.normalizedIndicator_apply μ K hK
  have hmass : (∫ y, e y ∂μ) = 1 := by
    simp_rw [he]
    rw [integral_const_mul, integral_indicator_const _ K.isOpen.measurableSet,
      Complex.real_smul, mul_one]
    exact inv_mul_cancel₀ (Hecke.HeckeAlgebra.compactOpen_complex_mass_ne_zero μ K hK)
  refine LinearMap.mem_range.mpr ⟨leftTestFunction T e, ?_⟩
  rw [← convolution_testDensity_left μ T e]
  ext φ
  rw [convolution_eq_pairing]
  have hpair : compactSupportPairing T (compactPartial (compactTestDensity μ e)
      (mulFunction ⟨(φ : G → ℂ), φ.locallyConstant⟩)) =
      D (SchwartzBruhat.partialIntegral (leftDensityKernel e φ) μ) := by
    apply compactSupportPairing_eq_of_agrees
    intro x _
    let h : LocallyConstant G ℂ := ⟨fun y => φ (x * y),
      φ.locallyConstant.comp_continuous (continuous_const.mul continuous_id)⟩
    change (∫ y, e y * h y ∂μ) = compactSupportPairing (compactTestDensity μ e) h
    exact (compactSupportPairing_testDensity μ e h).symm
  rw [hpair, distribution_partialIntegral μ]
  have hslice : ∀ y, D (SchwartzBruhat.sliceFst (leftDensityKernel e φ) y) = e y * D φ := by
    intro y
    have hs : SchwartzBruhat.sliceFst (leftDensityKernel e φ) y =
        e y • GroupAction.rightTests y φ := by
      ext x
      simp [leftDensityKernel]
    rw [hs, map_smul, smul_eq_mul]
    by_cases hy : y ∈ (K : Set G)
    · congr 1
      have hfix := LinearMap.congr_fun
        ((mem_fixed_iff _ _ _).mp hDr ⟨y⁻¹, K.toSubgroup.inv_mem hy⟩) φ
      change D (GroupAction.rightTests (y⁻¹)⁻¹ φ) = D φ at hfix
      rwa [inv_inv] at hfix
    · rw [he y, Set.indicator_of_notMem hy, mul_zero, zero_mul, zero_mul]
  simp_rw [hslice]
  rw [integral_mul_const, hmass, one_mul]

theorem right_subset_range :
    (uniformCompactDistributionsRight : Set (Distribution G)) ⊆
      LinearMap.range (testDensity μ) := by
  rintro D ⟨K, hK, hD⟩
  exact mem_range_of_right μ hK hD

theorem left_subset_range :
    (uniformCompactDistributionsLeft : Set (Distribution G)) ⊆
      LinearMap.range (testDensity μ) := by
  rintro D ⟨K, hK, hD⟩
  rw [compactDistributionsLeft, Submodule.mem_inf] at hD
  have hinv : GroupAction.inversionDistributions D ∈
      compactDistributionsRight K.toSubgroup := by
    rw [compactDistributionsRight, Submodule.mem_inf]
    exact ⟨inversion_mem_compactlySupported hD.1, inversion_mem_distributionsRight hD.2⟩
  obtain ⟨f, hf⟩ := LinearMap.mem_range.mp (mem_range_of_right μ hK hinv)
  obtain ⟨g, -, hg⟩ := inversion_testDensity μ f
  refine LinearMap.mem_range.mpr ⟨g, ?_⟩
  rw [← hg, hf, GroupAction.inversionDistributions_inversionDistributions]

theorem range_subset_both :
    (LinearMap.range (testDensity μ) : Set (Distribution G)) ⊆
      uniformCompactDistributionsBoth := by
  intro D hD
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hD
  exact testDensity_mem_compactDistributionsBoth μ f

omit [MeasurableSpace G] [BorelSpace G] in
theorem both_subset_left :
    (uniformCompactDistributionsBoth : Set (Distribution G)) ⊆
      uniformCompactDistributionsLeft := by
  rintro D ⟨K, hK, hD⟩
  refine ⟨K, hK, ?_⟩
  rw [compactDistributionsBoth, Submodule.mem_inf, distributionsBoth, Submodule.mem_inf] at hD
  rw [compactDistributionsLeft, Submodule.mem_inf]
  exact ⟨hD.1, hD.2.1⟩

omit [MeasurableSpace G] [BorelSpace G] in
theorem both_subset_right :
    (uniformCompactDistributionsBoth : Set (Distribution G)) ⊆
      uniformCompactDistributionsRight := by
  rintro D ⟨K, hK, hD⟩
  refine ⟨K, hK, ?_⟩
  rw [compactDistributionsBoth, Submodule.mem_inf, distributionsBoth, Submodule.mem_inf] at hD
  rw [compactDistributionsRight, Submodule.mem_inf]
  exact ⟨hD.1, hD.2.2⟩

end Measure

section Dirac

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- A uniformly left invariant Dirac forces the trivial subgroup to be open. -/
theorem discrete_of_dirac_mem {g : G}
    (h : dirac g ∈ uniformCompactDistributionsLeft (G := G)) : DiscreteTopology G := by
  obtain ⟨K, -, hK⟩ := h
  rw [compactDistributionsLeft, Submodule.mem_inf] at hK
  have hsub : (K : Set G) ⊆ {1} := by
    intro k hk
    by_contra hk1
    have hne : k * g ≠ g := by
      intro hkg
      apply hk1
      rw [Set.mem_singleton_iff]
      simpa using hkg
    obtain ⟨φ, hφ⟩ := exists_test_separating hne
    apply hφ
    have hfix := LinearMap.congr_fun ((mem_fixed_iff _ _ _).mp hK.2 ⟨k, hk⟩) φ
    simpa using hfix
  have hone : (K : Set G) = {1} :=
    Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr K.one_mem)
  apply discreteTopology_of_isOpen_singleton_one
  rw [← hone]
  exact K.isOpen

/-- In a discrete group every Dirac is invariant under the compact open trivial subgroup. -/
theorem dirac_mem_left_of_discrete [DiscreteTopology G] (g : G) :
    dirac g ∈ uniformCompactDistributionsLeft (G := G) := by
  let K : OpenSubgroup G := { toSubgroup := ⊥, isOpen' := isOpen_discrete _ }
  refine ⟨K, ?_, ?_⟩
  · change IsCompact ((⊥ : Subgroup G) : Set G)
    rw [Subgroup.coe_bot]
    exact isCompact_singleton
  · rw [compactDistributionsLeft, Submodule.mem_inf]
    refine ⟨(compactDirac g).property, ?_⟩
    rw [mem_fixed_iff]
    intro k
    have hk : (k : G) = 1 := Subgroup.mem_bot.mp k.property
    rw [hk, map_one]
    rfl

end Dirac

theorem uniformRange : UniformRangeStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _
  have hRB := range_subset_both μ
  have hBL := both_subset_left (G := G)
  have hBR := both_subset_right (G := G)
  have hLR := left_subset_range μ
  have hRtR := right_subset_range μ
  refine ⟨testDensity_injective μ, ?_, ?_, ?_⟩
  · exact Set.Subset.antisymm (hRB.trans hBL) hLR
  · exact Set.Subset.antisymm (hLR.trans (hRB.trans hBR)) (hRtR.trans (hRB.trans hBL))
  · exact Set.Subset.antisymm (hLR.trans hRB) hBL

theorem diracMembership : DiracMembershipStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ g
  have hL := (uniformRange G μ).2.1
  constructor
  · intro h
    apply discrete_of_dirac_mem (g := g)
    rw [← hL]
    exact h
  · intro h
    have hmem : dirac g ∈ (LinearMap.range (testDensity μ) : Set (Distribution G)) := by
      rw [hL]
      exact dirac_mem_left_of_discrete g
    exact hmem

theorem unitCriterion : UnitCriterionStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _
  constructor
  · rintro ⟨e, he⟩
    apply (diracMembership G μ 1).mp
    refine LinearMap.mem_range.mpr ⟨(e : SchwartzBruhat G), ?_⟩
    ext φ
    have h := congrArg (fun F : Hecke.HeckeAlgebra μ => F 1)
      (he (Hecke.TestFunction.inversion φ)).1
    change (∫ y, (e : SchwartzBruhat G) y * φ ((y⁻¹ * 1)⁻¹) ∂μ) = φ 1⁻¹ at h
    simp only [mul_one, inv_inv, inv_one] at h
    exact h
  · intro hdisc
    obtain ⟨e, he⟩ := LinearMap.mem_range.mp ((diracMembership G μ 1).mpr hdisc)
    refine ⟨e, fun h => ⟨?_, ?_⟩⟩
    · apply testDensity_injective μ
      obtain ⟨F, H, hF, hH, hFH⟩ := RenardConvolution.heckeCompatibility G μ e h
      have hF1 : F = compactDirac 1 := Subtype.ext (hF.trans he)
      change testDensity μ (Hecke.TestFunction.convolution μ e h) = testDensity μ h
      rw [← hFH, hF1, convolution_dirac_one_left, hH]
    · apply testDensity_injective μ
      obtain ⟨F, H, hF, hH, hFH⟩ := RenardConvolution.heckeCompatibility G μ h e
      have hH1 : H = compactDirac 1 := Subtype.ext (hH.trans he)
      change testDensity μ (Hecke.TestFunction.convolution μ h e) = testDensity μ h
      rw [← hFH, hH1, convolution_dirac_one_right, hF]

theorem ideal : IdealStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ T D hD
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hD
  have hrange := (uniformRange G μ).2.1
  refine ⟨compactTestDensity μ f, rfl, ?_, ?_⟩
  · rw [convolution_testDensity_left μ T f]
    exact LinearMap.mem_range_self _ _
  · obtain ⟨K, hK, hboth⟩ := testDensity_mem_compactDistributionsBoth μ f
    rw [compactDistributionsBoth, Submodule.mem_inf, distributionsBoth,
      Submodule.mem_inf] at hboth
    have hleft := hboth.2.1
    have hmem : (convolution (compactTestDensity μ f) T : Distribution G) ∈
        uniformCompactDistributionsLeft (G := G) := by
      refine ⟨K, hK, ?_⟩
      rw [compactDistributionsLeft, Submodule.mem_inf]
      refine ⟨(convolution _ T).property, ?_⟩
      rw [mem_fixed_iff]
      intro k
      have hk : convolution (compactDirac (k : G)) (compactTestDensity μ f) =
          compactTestDensity μ f := by
        apply Subtype.ext
        rw [convolution_dirac_left]
        exact (mem_fixed_iff _ _ _).mp hleft k
      rw [← convolution_dirac_left, ← convolution_associative, hk]
    have hmem' : (convolution (compactTestDensity μ f) T : Distribution G) ∈
        (LinearMap.range (testDensity μ) : Set (Distribution G)) := by
      rw [hrange]
      exact hmem
    exact hmem'

theorem inversionDensity : InversionDensityStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ f
  exact inversion_testDensity μ f

/-- Renard II.3.12: all five published assertions at the full group universe. -/
theorem statements : Statements.{uG} :=
  ⟨uniformRange, diracMembership, unitCriterion, ideal, inversionDensity⟩

end Langlands.HarmonicAnalysis.Distribution.RenardUniformDensity
