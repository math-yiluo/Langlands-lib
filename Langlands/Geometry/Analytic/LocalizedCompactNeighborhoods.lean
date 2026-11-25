import Langlands.Geometry.Analytic.ContinuousAnalyticAction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalLaurentNeighborhoods
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain
import Langlands.Sheaf.Equivariant.SmoothPart

/-! # Stable compact neighborhoods on actual localized analytic spaces -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

open CategoryTheory Set Filter Topology
open scoped Topology Pointwise

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {Y : Type v} [TopologicalSpace Y] (a : IndexedAffinoidAtlas.{u, v, w} K Y)

include a in
/-- Compact chart images in the actual atlas give compact neighborhoods. -/
theorem weaklyLocallyCompactSpace : WeaklyLocallyCompactSpace Y :=
  a.isNet_chartFamily.1.weaklyLocallyCompactSpace
    (fun V hV => (a.isCompactFamily_chartFamily V hV).1)

include a in
/-- Hausdorffness upgrades these compact neighborhoods to local compactness. -/
theorem locallyCompactSpace [T2Space Y] : LocallyCompactSpace Y := by
  have := a.weaklyLocallyCompactSpace
  infer_instance

/-- Saturation makes finite unions of original charts a neighborhood basis. -/
theorem HasAllLocalDomains.exists_finite_chart_nhds_subset
    (ha : a.HasAllLocalDomains) (x : Y) (U : Set Y) (hU : U ∈ 𝓝 x) :
    ∃ I : Set a.Index, I.Finite ∧
      (∀ i ∈ I, x ∈ Set.range (a.chart i) ∧ Set.range (a.chart i) ⊆ U) ∧
      (⋃ i ∈ I, Set.range (a.chart i)) ∈ 𝓝 x := by
  obtain ⟨σ, hσfin, hστ, hxσ, hσN⟩ := a.isNet_chartFamily.1 x
  have key : ∀ V ∈ σ, ∃ j : a.Index,
      x ∈ Set.range (a.chart j) ∧ Set.range (a.chart j) ⊆ U ∧
      ∃ t ∈ 𝓝 x, t ∩ V ⊆ Set.range (a.chart j) := by
    intro V hV
    obtain ⟨i, rfl⟩ := hστ hV
    obtain ⟨s, hs⟩ := hxσ _ hV
    have hpre : a.chart i ⁻¹' U ∈ 𝓝 s :=
      (a.isEmbedding_chart i).continuous.continuousAt.preimage_mem_nhds (hs ▸ hU)
    obtain ⟨d, hdN, hdU⟩ := PresentedAffinoidAlgebra.RationalChart.exists_rational_neighborhood
      s _ hpre
    obtain ⟨j, hj⟩ := ha.exists_chart (⟨i, d.toDomain⟩ : LocalDomain a)
    have hj' : Set.range (a.chart j) = a.chart i '' d.locus := hj
    refine ⟨j, ?_, ?_, ?_⟩
    · rw [hj']
      exact ⟨s, mem_of_mem_nhds hdN, hs⟩
    · rw [hj']
      rintro _ ⟨s', hs', rfl⟩
      exact hdU hs'
    · rw [(a.isEmbedding_chart i).nhds_eq_comap, Filter.mem_comap] at hdN
      obtain ⟨t, ht, hts⟩ := hdN
      refine ⟨t, hs ▸ ht, ?_⟩
      rintro y ⟨hyt, s', rfl⟩
      rw [hj']
      exact ⟨s', hts hyt, rfl⟩
  choose i hix hiU t ht hti using key
  refine ⟨{i' | ∃ V hV, i V hV = i'}, hσfin.dependent_image i, ?_, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    exact ⟨hix V hV, hiU V hV⟩
  · have hT : ⋂₀ {t' | ∃ V hV, t V hV = t'} ∈ 𝓝 x := by
      refine (Filter.sInter_mem (hσfin.dependent_image t)).2 ?_
      rintro _ ⟨V, hV, rfl⟩
      exact ht V hV
    refine Filter.mem_of_superset (Filter.inter_mem hσN hT) ?_
    rintro y ⟨⟨V, hV, hyV⟩, hyt⟩
    exact Set.mem_biUnion (⟨V, hV, rfl⟩ : ∃ V' hV', i V' hV' = i V hV)
      (hti V hV ⟨hyt _ ⟨V, hV, rfl⟩, hyV⟩)

end IndexedAffinoidAtlas

namespace SaturatedAtlasPresentation

variable (X : LocalizedCategory.{u, v, w} (K := K))

/-- The existing localized-space functor retains the atlas compact neighborhoods. -/
theorem weaklyLocallyCompactSpace_localized :
    WeaklyLocallyCompactSpace (localizedSpaceFunctor.obj X) :=
  (presentationOf X).presentation.atlas.weaklyLocallyCompactSpace

/-- Every Hausdorff actual localized analytic space is locally compact. -/
theorem locallyCompactSpace_localized [T2Space (localizedSpaceFunctor.obj X)] :
    LocallyCompactSpace (localizedSpaceFunctor.obj X) := by
  have := weaklyLocallyCompactSpace_localized X
  infer_instance

variable {X} {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (ρ : G →* Aut X)

/-- The action on the actual underlying topological space. -/
@[instance_reducible]
def localizedSpaceAction : MulAction G (localizedSpaceFunctor.obj X) where
  smul g x := localizedSpaceFunctor.map (ρ g).asIso.hom x
  one_smul x := by
    change localizedSpaceFunctor.map (ρ 1).asIso.hom x = x
    rw [map_one]
    change localizedSpaceFunctor.map (𝟙 X) x = x
    rw [CategoryTheory.Functor.map_id]
    rfl
  mul_smul g h x := by
    change localizedSpaceFunctor.map (ρ (g * h)).asIso.hom x =
      localizedSpaceFunctor.map (ρ g).asIso.hom (localizedSpaceFunctor.map (ρ h).asIso.hom x)
    rw [map_mul]
    change localizedSpaceFunctor.map ((ρ h).asIso.hom ≫ (ρ g).asIso.hom) x = _
    rw [CategoryTheory.Functor.map_comp]
    rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Each action map is continuous for the existing topology. -/
theorem continuousConstSMul_localizedSpaceAction :
    letI := localizedSpaceAction ρ
    ContinuousConstSMul G (localizedSpaceFunctor.obj X) := by
  let := localizedSpaceAction ρ
  exact ⟨fun g => (localizedSpaceFunctor.map (ρ g).asIso.hom).hom.continuous⟩

/-- Zero-function tests make the full setwise stabilizer of each chart open. -/
def chartOpenStabilizer (hρ : IsContinuousAction ρ)
    (i : (presentationOf X).presentation.atlas.Index) : OpenSubgroup G := by
  letI := localizedSpaceAction ρ
  let S : Set (localizedSpaceFunctor.obj X) :=
    Set.range ((presentationOf X).presentation.atlas.chart i)
  let H : Subgroup G := MulAction.stabilizer G S
  refine ⟨H, H.isOpen_of_mem_nhds (g := (1 : G)) ?_⟩
  let τ : TestTriple (presentationOf X) := ⟨i, 0, 1, zero_lt_one⟩
  apply Filter.mem_of_superset (hρ τ)
  intro g hg
  have heq := (hg : IsNear τ (ρ g).asIso.hom (𝟙 X)).preimage_eq
  have hpre : (fun x : localizedSpaceFunctor.obj X => g • x) ⁻¹' S = S := by
    change (localizedSpaceFunctor.map (ρ g).asIso.hom : _ → _) ⁻¹' S =
      (localizedSpaceFunctor.map (𝟙 X) : _ → _) ⁻¹' S at heq
    rw [CategoryTheory.Functor.map_id] at heq
    exact heq
  change g • S = S
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    change x ∈ (fun x : localizedSpaceFunctor.obj X => g • x) ⁻¹' S
    rw [hpre]
    exact hx
  · intro y hy
    refine ⟨g⁻¹ • y, ?_, smul_inv_smul g y⟩
    rw [← hpre]
    simpa using hy

/-- Berkovich continuity gives stable open neighborhoods for the actual space. -/
theorem hasStableNeighbourhoods_localizedSpaceAction (hρ : IsContinuousAction ρ) :
    letI := localizedSpaceAction ρ
    Langlands.Sheaf.Equivariant.HasStableNeighbourhoods G (localizedSpaceFunctor.obj X) := by
  let := localizedSpaceAction ρ
  have := continuousConstSMul_localizedSpaceAction ρ
  refine ⟨fun x O hO hx => ?_⟩
  let a := (presentationOf X).presentation.atlas
  obtain ⟨I, hI, hsub, hN⟩ :=
    IndexedAffinoidAtlas.HasAllLocalDomains.exists_finite_chart_nhds_subset a
      (presentationOf X).hasAllLocalDomains x O (hO.mem_nhds hx)
  let S : Set (localizedSpaceFunctor.obj X) := ⋃ i ∈ I, Set.range (a.chart i)
  let := hI.fintype
  let H : OpenSubgroup G := OpenSubgroup.iInfOfFinite
    (fun i : I => chartOpenStabilizer ρ hρ i.val)
  have hHS : ∀ g ∈ H, g • S = S := by
    intro g hg
    have hi : ∀ i ∈ I,
        g • (Set.range (a.chart i) : Set (localizedSpaceFunctor.obj X)) =
          Set.range (a.chart i) := by
      intro i hi
      exact OpenSubgroup.iInfOfFinite_le
        (fun i : I => chartOpenStabilizer ρ hρ i.val) ⟨i, hi⟩ hg
    apply Set.Subset.antisymm
    · rintro y ⟨t, ht, rfl⟩
      obtain ⟨i, hiI, hti⟩ := Set.mem_iUnion₂.1 ht
      exact Set.mem_iUnion₂.2 ⟨i, hiI, hi i hiI ▸ Set.smul_mem_smul_set hti⟩
    · intro y hy
      obtain ⟨i, hiI, hyi⟩ := Set.mem_iUnion₂.1 hy
      obtain ⟨t, hti, hgt⟩ := (hi i hiI).symm ▸ hyi
      exact ⟨t, Set.mem_iUnion₂.2 ⟨i, hiI, hti⟩, hgt⟩
  refine ⟨H, interior S, isOpen_interior, mem_interior_iff_mem_nhds.2 hN,
    interior_subset.trans (Set.iUnion₂_subset fun i hi => (hsub i hi).2), ?_⟩
  intro g hg y hy
  have hV : g • interior S = interior S := by
    rw [← interior_smul, hHS g hg]
  exact hV ▸ Set.smul_mem_smul_set hy

/-- A compact subset has a relatively compact stable open neighborhood inside
any prescribed open neighborhood, for independent group and space universes. -/
theorem exists_compact_stable_neighbourhood_localizedSpaceAction
    [T2Space (localizedSpaceFunctor.obj X)] (hρ : IsContinuousAction ρ)
    {C : Set (localizedSpaceFunctor.obj X)} (hC : IsCompact C)
    (U : TopologicalSpace.Opens (localizedSpaceFunctor.obj X)) (hCU : C ⊆ U) :
    letI := localizedSpaceAction ρ
    ∃ (V : TopologicalSpace.Opens (localizedSpaceFunctor.obj X)) (H : OpenSubgroup G),
      C ⊆ V ∧ closure (V : Set (localizedSpaceFunctor.obj X)) ⊆ U ∧
        IsCompact (closure (V : Set (localizedSpaceFunctor.obj X))) ∧
          ∀ g ∈ H, ∀ y ∈ V, g • y ∈ V := by
  classical
  let := localizedSpaceAction ρ
  have := locallyCompactSpace_localized X
  have := hasStableNeighbourhoods_localizedSpaceAction ρ hρ
  obtain ⟨W, hW, hCW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hC U.isOpen hCU
  choose H V hV hxV hVW hHV using fun x : C =>
    Langlands.Sheaf.Equivariant.HasStableNeighbourhoods.exists_stable
      (G := G) x.1 W hW (hCW x.2)
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover V hV (fun x hx =>
    Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  let O : TopologicalSpace.Opens (localizedSpaceFunctor.obj X) :=
    ⟨⋃ i ∈ s, V i, isOpen_biUnion fun i _ => hV i⟩
  let J : OpenSubgroup G := OpenSubgroup.iInfOfFinite (fun i : s => H i.1)
  have hOW : (O : Set (localizedSpaceFunctor.obj X)) ⊆ W := by
    intro y hy
    obtain ⟨i, _, hi⟩ := Set.mem_iUnion₂.1 hy
    exact hVW i hi
  refine ⟨O, J, hs, (closure_mono hOW).trans hWU,
    hWc.of_isClosed_subset isClosed_closure (closure_mono hOW), ?_⟩
  intro g hg y hy
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 hy
  exact Set.mem_iUnion₂.2 ⟨i, hi,
    hHV i g (OpenSubgroup.iInfOfFinite_le (fun i : s => H i.1) ⟨i, hi⟩ hg) y hyi⟩

end SaturatedAtlasPresentation
end Langlands.Analytic
