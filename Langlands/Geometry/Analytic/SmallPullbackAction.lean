import Langlands.Geometry.Analytic.ChartActionRestriction
import Langlands.Geometry.Analytic.FibreProductSmallSquare
import Langlands.Geometry.Analytic.PullbackActionTests

/-! # Continuous actions on the small strong fibre product -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Filter Set Topology BanachSpectrum PresentedAffinoidAlgebra
open AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section ChartMaps

variable {X Y : SaturatedAtlasPresentation.{u, v, v} K}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting a localized strong arrow computes its original bounded
pullback on the two selected charts. -/
theorem chartDomainPullback_restrict_map (a : X ⟶ Y)
    (i : X.presentation.atlas.Index) (j : Y.presentation.atlas.Index)
    (h : a.baseMap '' range (X.presentation.atlas.chart i) ⊆ range (Y.presentation.atlas.chart j)) :
    chartDomainPullback (X := localizationFunctor.obj X) (Y := localizationFunctor.obj Y) i j
      (domainRestrict (X := localizationFunctor.obj X) (Y := localizationFunctor.obj Y)
        (X.chartDomain i) (Y.chartDomain j) (localizationFunctor.map a)
        (fun x hx => h ⟨x, hx, rfl⟩)) = a.pullback i j h := by
  let D := X.chartDomain i
  let E := Y.chartDomain j
  have hchart : a.MapsOriginalDomainCharts D E := by
    intro k
    refine ⟨chartDomainFullChart Y j, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact h ⟨x, k.property hx, rfl⟩
  let b : X.domain D ⟶ Y.domain E := a.restrictDomains D E hchart
  have hb : localizationFunctor.map b =
      domainRestrict (X := localizationFunctor.obj X) (Y := localizationFunctor.obj Y)
        D E (localizationFunctor.map a) (fun x hx => h ⟨x, hx, rfl⟩) := by
    apply (cancel_mono (domainι (localizationFunctor.obj Y) E)).1
    rw [domainRestrict_comp]
    change localizationFunctor.map b ≫ localizationFunctor.map (Y.domainInclusion E) =
      localizationFunctor.map (X.domainInclusion D) ≫ localizationFunctor.map a
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg localizationFunctor.map (restrictDomains_comp_domainInclusion a D E hchart)
  rw [← hb, chartDomainPullback_localizationFunctor_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_saturationExtension_comp_original_heq
    {D : AffinoidAtlasPresentation.{u, v, v} K}
    (a : AffinoidAtlasPresentation.CompatibleStrongHom D X.presentation)
    (i : D.atlas.Index) (j : X.presentation.atlas.Index)
    (h : a.baseMap '' range (D.atlas.chart i) ⊆ range (X.presentation.atlas.chart j))
    (h' : ((a.saturationExtension : ofSaturation D ⟶ ofSaturation X.presentation) ≫
      X.saturationIso.hom : ofSaturation D ⟶ X).baseMap ''
      range (D.atlas.saturatedAtlas.chart (D.atlas.originalSaturatedIndex i)) ⊆
        range (X.presentation.atlas.chart j)) :
    HEq (((a.saturationExtension : ofSaturation D ⟶ ofSaturation X.presentation) ≫
      X.saturationIso.hom : ofSaturation D ⟶ X).pullback
      (D.atlas.originalSaturatedIndex i) j h') (a.pullback i j h) := by
  let I := D.atlas.originalSaturatedIndex i
  let J := X.presentation.atlas.originalSaturatedIndex j
  have hJ : X.saturationIso.hom.baseMap ''
      range (X.presentation.atlas.saturatedAtlas.chart J) ⊆
        range (X.presentation.atlas.chart j) := by
    change id '' range (X.presentation.atlas.saturatedAtlas.chart J) ⊆ _
    rw [image_id, X.presentation.atlas.saturatedAtlas_original_range]
  have hI := a.toStrongHom.saturationExtension_original_admissible i j h
  have hcomp := saturatedComp_pullback a.saturationExtension X.saturationIso.hom
    (ofSaturation D).hasAllLocalDomains (ofSaturation X.presentation).hasAllLocalDomains
    I J j hI hJ h'
  refine (heq_of_eq hcomp).trans ?_
  refine (BoundedAlgHom.comp_heq (D.atlas.saturatedAtlas_original_algebra i)
    (X.presentation.atlas.saturatedAtlas_original_algebra j) rfl
    (a.toStrongHom.saturationExtension_pullback_original a.coherent i j h)
    (X.presentation.directFromSaturation_pullback_original_heq j hJ)).trans ?_
  exact heq_of_eq (BoundedAlgHom.comp_id _)

end ChartMaps

section EquivariantCharts

variable {G : Type z} [Group G] [TopologicalSpace G]
  {U V : LocalizedCategory.{u, v, v} (K := K)}
  {σU : G →* Aut U} {σV : G →* Aut V}

private theorem eventually_chart_preimage_eq (hV : IsContinuousAction σV)
    (j : (presentationOf V).presentation.atlas.Index) :
    ∀ᶠ t in 𝓝 (1 : G), localizedSpaceFunctor.map (σV t).asIso.hom ⁻¹'
      ((presentationOf V).chartDomain j).carrier = ((presentationOf V).chartDomain j).carrier := by
  let τ : TestTriple (presentationOf V) := ⟨j, 0, 1, zero_lt_one⟩
  filter_upwards [hV τ] with t ht
  have ht' := (show IsNear τ (σV t).asIso.hom (𝟙 V) from ht).preimage_eq
  rw [CategoryTheory.Functor.map_id, TopCat.coe_id] at ht'
  exact ht'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem spectralConvergesOn_chartDomainPullback_of_equivariant
    (p : U ⟶ V) (hp : ∀ t, (σU t).asIso.hom ≫ p = p ≫ (σV t).asIso.hom)
    (i : (presentationOf U).presentation.atlas.Index) (j : (presentationOf V).presentation.atlas.Index)
    (himg : ∀ x ∈ ((presentationOf U).chartDomain i).carrier,
      localizedSpaceFunctor.map p x ∈ ((presentationOf V).chartDomain j).carrier)
    (hpres : ∀ᶠ t in 𝓝 (1 : G), localizedSpaceFunctor.map (σU t).asIso.hom ⁻¹'
      ((presentationOf U).chartDomain i).carrier = ((presentationOf U).chartDomain i).carrier)
    (hV : IsContinuousAction σV) (b : (presentationOf V).presentation.atlas.algebra j) :
    SpectralConvergesOn (𝓝 (1 : G)) (fun t => preservedChartPullback i (σU t).asIso.hom)
      (BoundedAlgHom.id K _)
      (chartDomainPullback i j (domainRestrict _ _ p himg) b) := by
  intro ε hε
  filter_upwards [hpres, eventually_chart_preimage_eq hV j,
    hV.spectralConvergesOn_preservedChartPullback j b ε hε] with t hi hj hb
  let D := (presentationOf U).chartDomain i
  let E := (presentationOf V).chartDomain j
  let e := domainι U D
  let d := domainι V E
  let p' := domainRestrict D E p himg
  let a := domainRestrict D D (σU t).asIso.hom (mapsTo_chart_of_preimage_eq i _ hi)
  let c := domainRestrict E E (σV t).asIso.hom (mapsTo_chart_of_preimage_eq j _ hj)
  have hp' : p' ≫ d = e ≫ p := domainRestrict_comp _ _ _ _
  have ha : a ≫ e = e ≫ (σU t).asIso.hom := domainRestrict_comp _ _ _ _
  have hc : c ≫ d = d ≫ (σV t).asIso.hom := domainRestrict_comp _ _ _ _
  have heq : a ≫ p' = p' ≫ c := by
    apply (cancel_mono d).1
    calc
      (a ≫ p') ≫ d = (a ≫ e) ≫ p := by rw [Category.assoc, hp', ← Category.assoc]
      _ = e ≫ p ≫ (σV t).asIso.hom := by rw [ha, Category.assoc, hp]
      _ = (p' ≫ d) ≫ (σV t).asIso.hom := by rw [hp', Category.assoc]
      _ = (p' ≫ c) ≫ d := by rw [Category.assoc, Category.assoc, hc]
  have hcomm := congrArg (chartDomainPullback i j) heq
  rw [chartDomainPullback_comp, chartDomainPullback_comp] at hcomm
  let m := chartDomainPullback i j p'
  have happly := congrArg (fun f : BoundedAlgHom K _ _ => f b) hcomm
  change chartDomainPullback i i a (m b) = m (chartDomainPullback j j c b) at happly
  change SpectralBound (preservedChartPullback i (σU t).asIso.hom (m b) - m b) ε
  rw [preservedChartPullback_of_preimage_eq _ _ hi, happly, ← map_sub]
  rw [preservedChartPullback_of_preimage_eq _ _ hj] at hb
  exact hb.map m.toBoundedRingHom

end EquivariantCharts

omit [CompleteSpace K] in
private theorem spectralConvergesOn_of_pushout_heq
    {A B C E : PresentedAffinoidAlgebra K} {T : Type z} {l : Filter T}
    (f : BoundedAlgHom K C A) (g : BoundedAlgHom K C B)
    (hE : E = AffinoidPushout.algebra f g)
    (φ : T → BoundedAlgHom K E E)
    (p : BoundedAlgHom K A E) (q : BoundedAlgHom K B E)
    (hp : HEq p (AffinoidPushout.leftMap f g)) (hq : HEq q (AffinoidPushout.rightMap f g))
    (hl : ∀ a : A, SpectralConvergesOn l φ (BoundedAlgHom.id K E) (p a))
    (hr : ∀ b : B, SpectralConvergesOn l φ (BoundedAlgHom.id K E) (q b))
    (c : E) : SpectralConvergesOn l φ (BoundedAlgHom.id K E) c := by
  subst E
  obtain rfl : p = AffinoidPushout.leftMap f g := eq_of_heq hp
  obtain rfl : q = AffinoidPushout.rightMap f g := eq_of_heq hq
  exact AffinoidPushout.spectralConvergesOn_of_factors f g hl hr c

section SmallProduct

variable {X Y S : SaturatedAtlasPresentation.{u, v, v} K}
  (f : X ⟶ S) (g : Y ⟶ S)
  [Small.{v} (FibreProduct.chartSystem (geometricCompatibleMap f) (geometricCompatibleMap g)).Space]

local notation "F" => geometricCompatibleMap f
local notation "G₀" => geometricCompatibleMap g
local notation "A" => FibreProduct.smallPresentation F G₀
  X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains
local notation "P" => smallFibreProduct f g
local notation "p" => smallFibreProductFst f g
local notation "q" => smallFibreProductSnd f g
local notation "r" => FibreProduct.smallRep F G₀
  X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains

/-- The original small fibre-product charts in the saturated product. -/
def smallFibreProductChart (i : (A).atlas.Index) : (P).presentation.atlas.Index :=
  (A).atlas.originalSaturatedIndex i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual chart of an original pair is the simultaneous preimage of
the two projected chart ranges. -/
theorem range_smallFibreProductChart (i : (A).atlas.Index) :
    range ((P).presentation.atlas.chart (smallFibreProductChart f g i)) =
      (p).baseMap ⁻¹' range (X.presentation.atlas.chart (r i).val.1) ∩
        (q).baseMap ⁻¹' range (Y.presentation.atlas.chart (r i).val.2) := by
  let e := FibreProduct.smallSpaceHomeomorph F G₀
    X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains
  change range ((A).atlas.saturatedAtlas.chart ((A).atlas.originalSaturatedIndex i)) = _
  rw [(A).atlas.saturatedAtlas_original_range]
  ext z
  obtain ⟨z, rfl⟩ := e.surjective z
  have hchart : e z ∈ range ((A).atlas.chart i) ↔
      z ∈ range ((FibreProduct.chartSystem F G₀).chart (r i)) := by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, e.injective hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  rw [hchart, FibreProduct.mem_range_chart_iff]
  change _ ↔ FibreProduct.fst F G₀ (e.symm (e z)) ∈
      range (X.presentation.atlas.chart (r i).val.1) ∧
    FibreProduct.snd F G₀ (e.symm (e z)) ∈ range (Y.presentation.atlas.chart (r i).val.2)
  rw [e.symm_apply_apply]

theorem exists_smallFibreProductChart_contains (j : (P).presentation.atlas.Index) :
    ∃ i : (A).atlas.Index, range ((P).presentation.atlas.chart j) ⊆
      range ((P).presentation.atlas.chart (smallFibreProductChart f g i)) := by
  change (A).atlas.localDomainFamily at j
  let D := (A).atlas.saturatedRepresentative j
  refine ⟨D.index, ?_⟩
  change range ((A).atlas.saturatedChart j) ⊆
    range ((A).atlas.saturatedAtlas.chart ((A).atlas.originalSaturatedIndex D.index))
  rw [(A).atlas.range_saturatedChart, (A).atlas.saturatedAtlas_original_range,
    ← (A).atlas.saturatedRepresentative_locus j]
  exact image_subset_range _ _

/-- The first projection retains the entire left map of the raw
affinoid pushout after the original chart is saturated. -/
theorem smallFibreProductFst_pullback_heq (i : (A).atlas.Index)
    (h : (p).baseMap '' range ((P).presentation.atlas.chart (smallFibreProductChart f g i)) ⊆
      range (X.presentation.atlas.chart (r i).val.1)) :
    HEq ((p).pullback (smallFibreProductChart f g i) (r i).val.1 h)
      (FibreProduct.leftMap F G₀ (r i)) := by
  let a := FibreProduct.smallFstHom F G₀ X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains
  have ha : a.baseMap '' range ((A).atlas.chart i) ⊆ range (X.presentation.atlas.chart (r i).val.1) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨_, (FibreProduct.smallFstBase_chart F G₀
      X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains i x).symm⟩
  refine (pullback_saturationExtension_comp_original_heq a i _ ha h).trans ?_
  change HEq (X.presentation.atlas.changeMapChart _ _ _ (FibreProduct.leftMap F G₀ (r i)) _)
    (FibreProduct.leftMap F G₀ (r i))
  exact heq_of_eq (X.presentation.atlas.changeMapChart_self _ _ _ _)

/-- The second projection retains the entire right map of the raw
affinoid pushout after the original chart is saturated. -/
theorem smallFibreProductSnd_pullback_heq (i : (A).atlas.Index)
    (h : (q).baseMap '' range ((P).presentation.atlas.chart (smallFibreProductChart f g i)) ⊆
      range (Y.presentation.atlas.chart (r i).val.2)) :
    HEq ((q).pullback (smallFibreProductChart f g i) (r i).val.2 h)
      (FibreProduct.rightMap F G₀ (r i)) := by
  let a := FibreProduct.smallSndHom F G₀ X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains
  have ha : a.baseMap '' range ((A).atlas.chart i) ⊆ range (Y.presentation.atlas.chart (r i).val.2) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨_, (FibreProduct.smallSndBase_chart F G₀
      X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains i x).symm⟩
  refine (pullback_saturationExtension_comp_original_heq a i _ ha h).trans ?_
  change HEq (Y.presentation.atlas.changeMapChart _ _ _ (FibreProduct.rightMap F G₀ (r i)) _)
    (FibreProduct.rightMap F G₀ (r i))
  exact heq_of_eq (Y.presentation.atlas.changeMapChart_self _ _ _ _)

variable {G : Type z} [Group G] [TopologicalSpace G]

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An action on the canonical small strong fibre product is continuous
when both projections intertwine continuous factor actions. -/
theorem isContinuousAction_smallFibreProduct
    (σ : G →* Aut (localizationFunctor.obj P))
    (σX : G →* Aut (localizationFunctor.obj X)) (σY : G →* Aut (localizationFunctor.obj Y))
    (hX : IsContinuousAction σX) (hY : IsContinuousAction σY)
    (hp : ∀ t, (σ t).asIso.hom ≫ localizationFunctor.map p =
      localizationFunctor.map p ≫ (σX t).asIso.hom)
    (hq : ∀ t, (σ t).asIso.hom ≫ localizationFunctor.map q =
      localizationFunctor.map q ≫ (σY t).asIso.hom) :
    IsContinuousAction σ := by
  apply isContinuousAction_of_chart_subsets σ
  intro i
  obtain ⟨k, hk⟩ := exists_smallFibreProductChart_contains f g i
  let I := smallFibreProductChart f g k
  let j := (r k).val.1
  let j' := (r k).val.2
  have hrange := range_smallFibreProductChart f g k
  have hpres : ∀ᶠ t in 𝓝 (1 : G), localizedSpaceFunctor.map (σ t).asIso.hom ⁻¹'
      ((P).chartDomain I).carrier = ((P).chartDomain I).carrier := by
    change ∀ᶠ t in 𝓝 (1 : G), localizedSpaceFunctor.map (σ t).asIso.hom ⁻¹'
      range ((P).presentation.atlas.chart I) = range ((P).presentation.atlas.chart I)
    rw [hrange]
    exact eventually_preimage_eq_pullback_patch hX hY _ _ hp hq j j'
  refine ⟨I, hk, hpres, ?_⟩
  intro b
  have hleft : (p).baseMap '' range ((P).presentation.atlas.chart I) ⊆
      range (X.presentation.atlas.chart j) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hrange.subset hx).1
  have hright : (q).baseMap '' range ((P).presentation.atlas.chart I) ⊆
      range (Y.presentation.atlas.chart j') := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hrange.subset hx).2
  have hl (c : X.presentation.atlas.algebra j) :
      SpectralConvergesOn (𝓝 (1 : G)) (fun t => preservedChartPullback I (σ t).asIso.hom)
        (BoundedAlgHom.id K _) ((p).pullback I j hleft c) := by
    rw [← chartDomainPullback_restrict_map p I j hleft]
    exact spectralConvergesOn_chartDomainPullback_of_equivariant _ hp I j _ hpres hX c
  have hr (c : Y.presentation.atlas.algebra j') :
      SpectralConvergesOn (𝓝 (1 : G)) (fun t => preservedChartPullback I (σ t).asIso.hom)
        (BoundedAlgHom.id K _) ((q).pullback I j' hright c) := by
    rw [← chartDomainPullback_restrict_map q I j' hright]
    exact spectralConvergesOn_chartDomainPullback_of_equivariant _ hq I j' _ hpres hY c
  let φ (t : G) : BoundedAlgHom K ((P).presentation.atlas.algebra I)
      ((P).presentation.atlas.algebra I) :=
    preservedChartPullback (X := localizationFunctor.obj P) I (σ t).asIso.hom
  exact spectralConvergesOn_of_pushout_heq (FibreProduct.leftBase F G₀ (r k))
    (FibreProduct.rightBase F G₀ (r k)) ((A).atlas.saturatedAtlas_original_algebra k)
    φ ((p).pullback I j hleft)
    ((q).pullback I j' hright) (smallFibreProductFst_pullback_heq f g k hleft)
    (smallFibreProductSnd_pullback_heq f g k hright) hl hr b

end SmallProduct

end Langlands.Analytic.SaturatedAtlasPresentation
