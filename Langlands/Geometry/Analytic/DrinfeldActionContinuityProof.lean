import Langlands.Geometry.Analytic.DrinfeldActionContinuityStatement
import Langlands.Geometry.Analytic.DrinfeldMemberAction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainNormSpectralTests

/-! # Proof: continuity of the action of `GL_{d+1}(F)` on Drinfeld's upper half space -/

noncomputable section

universe u v

namespace Langlands.Analytic.DrinfeldUpperHalfSpace

open Set Filter Topology CategoryTheory PresentedAffinoidAlgebra IndexedAffinoidAtlas
open SaturatedAtlasPresentation AffinoidAtlasPresentation

variable {F : Type v} [NontriviallyNormedField F] [ProperSpace F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] {d : ℕ} [NeZero d]

variable (F d) in
/-- The saturated presentation of `Ω` underlying `omegaAction F K d`. -/
abbrev omegaSaturated : SaturatedAtlasPresentation.{u, u, u} K :=
  SaturatedAtlasPresentation.ofSaturation (exhaustionPresentation F K d)

/-- The strong map of saturated presentations given by `γ`. -/
abbrev saturatedAction (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F) :
    omegaSaturated F K d ⟶ omegaSaturated F K d :=
  (compatibleHom K γ).saturationExtension

/-- The action of the stabilizer on spectrum points is the action of matrices on `Ω`. -/
theorem actionMap_exhaustionChartMap_smul (V : ExhaustionIndex F K d)
    (g : memberStabilizer K V)
    (x : BanachSpectrum (exhaustionChart F K d V.level).algebra) :
    actionMap K (g : Matrix.GeneralLinearGroup (Fin (d + 1)) F) (exhaustionChartMap F K d V x) =
      exhaustionChartMap F K d V (memberAction K V g • x) :=
  actionMap_exhaustionChartMap_selfPullback K V g.1 g.2 x

/-- If the action of `g` on the chart algebra of `V` preserves a represented domain `L`,
then `g` preserves the image of `L` in `Ω`, in the form of an inverse-image equality. -/
theorem preimage_image_eq_of_mem_locusStabilizer (V : ExhaustionIndex F K d)
    (g : memberStabilizer K V) (D : Domain K (exhaustionChart F K d V.level).algebra)
    (hg : memberAction K V g ∈ DomainAutomorphism.locusStabilizer D) :
    actionMap K (g : Matrix.GeneralLinearGroup (Fin (d + 1)) F) ⁻¹'
        (exhaustionChartMap F K d V '' D.locus) =
      exhaustionChartMap F K d V '' D.locus := by
  apply Set.Subset.antisymm
  · rintro z ⟨y, hy, hzy⟩
    have hzV : z.1 ∈ V.1 := by
      apply (g.2 z).1
      rw [← hzy]
      exact mem_exhaustionChartMap K V y
    have hz' : z ∈ range (exhaustionChartMap F K d V) := by
      rw [range_exhaustionChartMap]
      exact hzV
    obtain ⟨x, rfl⟩ := hz'
    rw [actionMap_exhaustionChartMap_smul] at hzy
    have hxy : memberAction K V g • x = y := injective_exhaustionChartMap F K d V hzy.symm
    refine ⟨x, ?_, rfl⟩
    have hinv : (memberAction K V g)⁻¹ ∈ DomainAutomorphism.locusStabilizer D :=
      Subgroup.inv_mem _ hg
    have := DomainAutomorphism.smul_mem_locus D ⟨_, hinv⟩ hy
    rw [← hxy] at this
    simpa only [inv_smul_smul] using this
  · rintro _ ⟨x, hx, rfl⟩
    rw [Set.mem_preimage, actionMap_exhaustionChartMap_smul]
    exact ⟨_, DomainAutomorphism.smul_mem_locus D ⟨_, hg⟩ hx, rfl⟩

/-- The bounded map of the original strong map from a preserved member to itself is the
self pullback. -/
theorem compatibleHom_pullback_self (V : ExhaustionIndex F K d)
    (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F) (hγ : γ ∈ memberStabilizer K V)
    (h : (compatibleHom K γ).baseMap '' Set.range ((exhaustionAtlas F K d).chart V) ⊆
      Set.range ((exhaustionAtlas F K d).chart V)) :
    (compatibleHom K γ).pullback V V h = selfPullback K V γ hγ := by
  have hs : Set.range ((exhaustionAtlas F K d).chart (targetIndex K γ V)) ⊆
      Set.range ((exhaustionAtlas F K d).chart V) :=
    (range_exhaustionChartMap_subset_iff F K d).2 (targetIndex_subset_of_mem K hγ)
  have e := AffinoidAtlasPresentation.CompatibleStrongHom.ofChain_pullback_upper
    (presentationHom K γ) (exhaustionAtlas_hasChainCharts K) V V h hs
  refine e.trans ?_
  exact (selfPullback_eq_of_isActionPullback K V γ hγ
    ((pullback_isActionPullback K γ V).comp_res (targetIndex_subset_of_mem K hγ))).symm

/-- A matrix preserving the member `V` maps the chart of `V` into itself. -/
theorem compatibleHom_image_chart_subset (V : ExhaustionIndex F K d)
    (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F) (hγ : γ ∈ memberStabilizer K V) :
    (compatibleHom K γ).baseMap '' Set.range ((exhaustionAtlas F K d).chart V) ⊆
      Set.range ((exhaustionAtlas F K d).chart V) := by
  rintro _ ⟨z, hz, rfl⟩
  have hz' : z ∈ range (exhaustionChartMap F K d V) := hz
  rw [range_exhaustionChartMap] at hz'
  show actionMap K γ z ∈ range (exhaustionChartMap F K d V)
  rw [range_exhaustionChartMap]
  exact (hγ z).2 hz'

section Test

variable {K}
variable (τ : TestTriple (omegaSaturated F K d))

/-- The index of the affinoid domain of a test triple, as a local-domain subset. -/
abbrev testIndex : (exhaustionAtlas F K d).localDomainFamily := τ.domain

/-- The chosen local domain representing the affinoid domain of a test triple. -/
abbrev testRepresentative : LocalDomain (exhaustionAtlas F K d) :=
  (exhaustionAtlas F K d).saturatedRepresentative (testIndex τ)

/-- The member of the exhaustion containing the affinoid domain of a test triple. -/
abbrev testMember : ExhaustionIndex F K d := (testRepresentative τ).index

/-- The represented domain of the chart algebra of `testMember τ`. -/
abbrev testDomain : Domain K (exhaustionChart F K d (testMember τ).level).algebra :=
  (testRepresentative τ).domain

/-- The function of a test triple, as a section of the represented domain. -/
abbrev testFunction : (testDomain τ).algebra := τ.function

theorem testLocus_eq :
    τ.locus = exhaustionChartMap F K d (testMember τ) '' (testDomain τ).locus := by
  change Set.range ((exhaustionAtlas F K d).saturatedChart (testIndex τ)) = _
  rw [(exhaustionAtlas F K d).range_saturatedChart, ←
    (exhaustionAtlas F K d).saturatedRepresentative_locus (testIndex τ)]
  rfl

/-- On the affinoid domain of the test triple, the pullback along `γ = g⁻¹` is the
section operator constructed from the action of `g` on the chart algebra. -/
theorem saturatedAction_pullback_self (g : memberStabilizer K (testMember τ))
    (hg : memberAction K (testMember τ) g ∈
      DomainAutomorphism.locusStabilizer (testDomain τ))
    (h : (saturatedAction K (g⁻¹ : memberStabilizer K (testMember τ)).1).baseMap ''
        Set.range ((omegaSaturated F K d).presentation.atlas.chart τ.domain) ⊆
      Set.range ((omegaSaturated F K d).presentation.atlas.chart τ.domain)) :
    (saturatedAction K (g⁻¹ : memberStabilizer K (testMember τ)).1).pullback
        τ.domain τ.domain h =
      DomainAutomorphism.stabilizerSectionMap (testDomain τ) ⟨_, hg⟩ := by
  have hγ : (g⁻¹ : memberStabilizer K (testMember τ)).1 ∈ memberStabilizer K (testMember τ) :=
    (g⁻¹).2
  have hR : (compatibleHom K (g⁻¹ : memberStabilizer K (testMember τ)).1).baseMap ''
      (testRepresentative τ).locus ⊆ (testRepresentative τ).locus := by
    have h' := h
    change _ '' Set.range ((exhaustionAtlas F K d).saturatedChart (testIndex τ)) ⊆
      Set.range ((exhaustionAtlas F K d).saturatedChart (testIndex τ)) at h'
    rw [(exhaustionAtlas F K d).range_saturatedChart, ←
      (exhaustionAtlas F K d).saturatedRepresentative_locus (testIndex τ)] at h'
    exact h'
  have hV := compatibleHom_image_chart_subset K (testMember τ) _ hγ
  apply DomainAutomorphism.boundedHom_ext (testDomain τ)
  refine (StrongHom.localDomainPullback_comp_baseMap
    (compatibleHom K (g⁻¹ : memberStabilizer K (testMember τ)).1).toStrongHom
    (testRepresentative τ) (testRepresentative τ) hR).trans ?_
  refine (StrongHom.localChartPullback_of_parent_admissible
    (compatibleHom K (g⁻¹ : memberStabilizer K (testMember τ)).1).toStrongHom
    (compatibleHom K (g⁻¹ : memberStabilizer K (testMember τ)).1).coherent
    (testRepresentative τ) (testMember τ) hV _).trans ?_
  refine Eq.trans ?_
    (DomainAutomorphism.stabilizerSectionMap_comp_baseMap (testDomain τ) ⟨_, hg⟩).symm
  exact congrArg (fun φ : BoundedAlgHom K (exhaustionChart F K d (testMember τ).level).algebra
      (exhaustionChart F K d (testMember τ).level).algebra => (testDomain τ).baseMap.comp φ)
    (compatibleHom_pullback_self K (testMember τ) _ hγ hV)

/-- If `g` lies in the spectral test subgroup of the test triple, then `γ = g⁻¹` is near the
identity for that triple. -/
theorem strongNear_of_mem (g : memberStabilizer K (testMember τ))
    (hD : memberAction K (testMember τ) g ∈ DomainAutomorphism.domainSpectralSubgroup
      (testDomain τ) (testFunction τ) τ.bound τ.bound_pos.le) :
    StrongNear τ (saturatedAction K (g⁻¹ : memberStabilizer K (testMember τ)).1)
      (𝟙 (omegaSaturated F K d)) := by
  obtain ⟨hg, hbound⟩ :=
    (DomainAutomorphism.mem_domainSpectralSubgroup _ _ _ _ _).mp hD
  have hg' : memberAction K (testMember τ) g⁻¹ ∈
      DomainAutomorphism.locusStabilizer (testDomain τ) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hg
  have hpre : (saturatedAction K (g⁻¹ : memberStabilizer K (testMember τ)).1).baseMap ⁻¹'
      τ.locus = τ.locus := by
    rw [testLocus_eq]
    exact preimage_image_eq_of_mem_locusStabilizer K (testMember τ) g⁻¹ (testDomain τ) hg'
  have hS : (saturatedAction K (g⁻¹ : memberStabilizer K (testMember τ)).1).baseMap ''
        Set.range ((omegaSaturated F K d).presentation.atlas.chart τ.domain) ⊆
      Set.range ((omegaSaturated F K d).presentation.atlas.chart τ.domain) := by
    rw [Set.image_subset_iff]
    change τ.locus ⊆ _ ⁻¹' τ.locus
    rw [hpre]
  have hId : (𝟙 (omegaSaturated F K d) : omegaSaturated F K d ⟶ _).baseMap ''
      Set.range ((omegaSaturated F K d).presentation.atlas.chart τ.domain) ⊆ τ.locus := by
    rw [baseMap_id, ContinuousMap.coe_id, Set.image_id]
    exact subset_rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hpre, baseMap_id, ContinuousMap.coe_id, Set.preimage_id]
  · intro y hy
    refine ⟨τ.domain, ⟨hS, hId⟩, ?_⟩
    rw [hpre] at hy
    exact hy
  · intro i hi p
    have hiS : Set.range ((omegaSaturated F K d).presentation.atlas.chart i) ⊆
        Set.range ((omegaSaturated F K d).presentation.atlas.chart τ.domain) := by
      have := hi.2
      rwa [baseMap_id, ContinuousMap.coe_id, Set.image_id] at this
    have hcomm := (saturatedAction K (g⁻¹ : memberStabilizer K (testMember τ)).1).restriction_comm
      i τ.domain τ.domain τ.domain hiS subset_rfl hi.1 hS
    rw [(omegaSaturated F K d).presentation.atlas.restriction_id, BoundedAlgHom.comp_id]
      at hcomm
    rw [← hcomm, saturatedAction_pullback_self τ g hg hS]
    change p ((omegaSaturated F K d).presentation.atlas.restriction i τ.domain hiS
        (DomainAutomorphism.stabilizerSectionMap (testDomain τ) ⟨_, hg⟩ τ.function) -
      (omegaSaturated F K d).presentation.atlas.restriction i τ.domain hiS τ.function) ≤ _
    have hsub := map_sub
      ((omegaSaturated F K d).presentation.atlas.restriction i τ.domain hiS).toAlgHom
      ((DomainAutomorphism.stabilizerSectionMap (testDomain τ) ⟨_, hg⟩).toAlgHom
        (testFunction τ)) (testFunction τ)
    refine (le_of_eq (congrArg p.toMulRingSeminorm hsub.symm)).trans ?_
    exact hbound (BanachSpectrum.comap
      ((omegaSaturated F K d).presentation.atlas.restriction i τ.domain hiS).toBoundedRingHom p)

/-- The near-identity relation for `γ = g⁻¹`, with identity fraction denominators. -/
theorem isNear_of_mem (g : memberStabilizer K (testMember τ))
    (hD : memberAction K (testMember τ) g ∈ DomainAutomorphism.domainSpectralSubgroup
      (testDomain τ) (testFunction τ) τ.bound τ.bound_pos.le) :
    IsNear (X := (omegaAction F K d).V) (Y := (omegaAction F K d).V) τ
      (localizationFunctor.map (saturatedAction K (g⁻¹ : memberStabilizer K (testMember τ)).1))
      (𝟙 _) :=
  ⟨omegaSaturated F K d, 𝟙 _, quasiIsomorphisms.id_mem _, saturatedAction K _, 𝟙 _,
    localizationFunctor_map_eq_fraction _,
    (localizedQuasiIso_inv_hom_id (𝟙 (omegaSaturated F K d)) (quasiIsomorphisms.id_mem _)).symm,
    strongNear_of_mem τ g hD⟩

end Test

theorem omegaAction_ρAut_hom (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F) :
    ((omegaAction F K d).ρAut γ).asIso.hom = localizationFunctor.map (saturatedAction K γ) := rfl

/-- Membership of `γ = g⁻¹` in the inverse image of Berkovich's set `G_τ(Ω)`. -/
theorem mem_preimage_nearIdentity_of_mem (τ : TestTriple (omegaSaturated F K d))
    (g : memberStabilizer K (testMember τ))
    (hgD : memberAction K (testMember τ) g ∈ DomainAutomorphism.domainSpectralSubgroup
      (testDomain τ) (testFunction τ) τ.bound τ.bound_pos.le) :
    (g⁻¹ : memberStabilizer K (testMember τ)).1 ∈
      (omegaAction F K d).ρAut ⁻¹' nearIdentity (X := (omegaAction F K d).V) τ := by
  rw [Set.mem_preimage]
  unfold SaturatedAtlasPresentation.nearIdentity
  rw [Set.mem_ofPred_eq, omegaAction_ρAut_hom]
  exact isNear_of_mem τ g hgD

/-- Each test triple gives an identity neighborhood of matrices near the identity. -/
theorem omegaAction_preimage_nearIdentity_mem_nhds (τ : TestTriple (omegaSaturated F K d)) :
    (omegaAction F K d).ρAut ⁻¹' nearIdentity (X := (omegaAction F K d).V) τ ∈
      𝓝 (1 : Matrix.GeneralLinearGroup (Fin (d + 1)) F) := by
  have hW := DomainAutomorphism.domainSpectralSubgroup_mem_nhds_of_normContinuous
    (memberAction K (testMember τ)) (continuous_memberAction K (testMember τ)) (testDomain τ)
    (testFunction τ) τ.bound τ.bound_pos
  have hmap := (isOpen_memberStabilizer K (testMember τ)).isOpenEmbedding_subtypeVal.map_nhds_eq
    (1 : memberStabilizer K (testMember τ))
  rw [OneMemClass.coe_one] at hmap
  have hW' : Subtype.val '' ((memberAction K (testMember τ)) ⁻¹'
      (DomainAutomorphism.domainSpectralSubgroup (testDomain τ) (testFunction τ) τ.bound
        τ.bound_pos.le : Set _)) ∈ 𝓝 (1 : Matrix.GeneralLinearGroup (Fin (d + 1)) F) := by
    rw [← hmap]
    exact Filter.image_mem_map hW
  have hinv : Tendsto (fun γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F => γ⁻¹)
      (𝓝 1) (𝓝 1) := by
    simpa only [inv_one] using
      (continuous_inv.tendsto (1 : Matrix.GeneralLinearGroup (Fin (d + 1)) F))
  filter_upwards [hinv hW'] with γ hγ
  obtain ⟨g, hgD, hgγ⟩ := hγ
  have hγg : γ = (g⁻¹ : memberStabilizer K (testMember τ)).1 := by
    rw [Subgroup.coe_inv, hgγ, inv_inv]
  subst hγg
  exact mem_preimage_nearIdentity_of_mem K τ g hgD

/-- **Continuity of the action of `GL_{d+1}(F)` on Drinfeld's upper half space.** -/
theorem omegaActionContinuity : OmegaActionContinuityStatement.{u, v} := by
  intro F _ _ K _ _ _ _ d _ τ
  exact omegaAction_preimage_nearIdentity_mem_nhds K τ

end Langlands.Analytic.DrinfeldUpperHalfSpace
