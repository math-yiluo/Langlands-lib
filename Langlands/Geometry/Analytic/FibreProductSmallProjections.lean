import Langlands.Geometry.Analytic.FibreProductSmallAtlas
import Langlands.Geometry.Analytic.FibreProductProjections

/-! # Complete compatible strong projections from the small fibre-product atlas -/

noncomputable section

universe u v

namespace Langlands.Analytic.FibreProduct

open Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, v} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)
  [Small.{v} (chartSystem f g).Space]
  (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
  (hC : C.atlas.HasAllLocalDomains)

/-- The original good pair underlying a shrunk atlas index. -/
def smallRep (T : (smallPresentation f g hA hB hC).atlas.Index) : PairIndex f g :=
  ((equivShrink (LocalAtlasIndex f g)).symm T).rep

/-- Charts of the small atlas retain the original spectrum points. -/
theorem small_chart (T : (smallPresentation f g hA hB hC).atlas.Index)
    (x : BanachSpectrum (algebra f g (smallRep f g hA hB hC T))) :
    (smallPresentation f g hA hB hC).atlas.chart T x =
      smallSpaceHomeomorph f g hA hB hC ((chartSystem f g).chart (smallRep f g hA hB hC T) x) := rfl

/-- Chart containment pulls back to literal containment in the original quotient. -/
theorem small_chart_subset (T T' : (smallPresentation f g hA hB hC).atlas.Index)
    (h : range ((smallPresentation f g hA hB hC).atlas.chart T) ⊆
      range ((smallPresentation f g hA hB hC).atlas.chart T')) :
    range ((chartSystem f g).chart (smallRep f g hA hB hC T)) ⊆
      range ((chartSystem f g).chart (smallRep f g hA hB hC T')) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := h ⟨x, rfl⟩
  exact ⟨y, (smallSpaceHomeomorph f g hA hB hC).injective hy⟩

/-- The actual first projection after the canonical space shrinking. -/
def smallFstBase : C((smallPresentation f g hA hB hC).space, A.space) :=
  (⟨fst f g, continuous_fst f g⟩ : C((chartSystem f g).Space, A.space)).comp
    ⟨(smallSpaceHomeomorph f g hA hB hC).symm,
      (smallSpaceHomeomorph f g hA hB hC).symm.continuous⟩

/-- The actual second projection after the canonical space shrinking. -/
def smallSndBase : C((smallPresentation f g hA hB hC).space, B.space) :=
  (⟨snd f g, continuous_snd f g⟩ : C((chartSystem f g).Space, B.space)).comp
    ⟨(smallSpaceHomeomorph f g hA hB hC).symm,
      (smallSpaceHomeomorph f g hA hB hC).symm.continuous⟩

theorem smallFstBase_chart (T : (smallPresentation f g hA hB hC).atlas.Index)
    (x : BanachSpectrum (algebra f g (smallRep f g hA hB hC T))) :
    smallFstBase f g hA hB hC ((smallPresentation f g hA hB hC).atlas.chart T x) =
      A.atlas.chart (smallRep f g hA hB hC T).val.1 (leftPoint f g (smallRep f g hA hB hC T) x) := by
  change fst f g ((smallSpaceHomeomorph f g hA hB hC).symm
    (smallSpaceHomeomorph f g hA hB hC ((chartSystem f g).chart _ x))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem smallSndBase_chart (T : (smallPresentation f g hA hB hC).atlas.Index)
    (x : BanachSpectrum (algebra f g (smallRep f g hA hB hC T))) :
    smallSndBase f g hA hB hC ((smallPresentation f g hA hB hC).atlas.chart T x) =
      B.atlas.chart (smallRep f g hA hB hC T).val.2 (rightPoint f g (smallRep f g hA hB hC T) x) := by
  change snd f g ((smallSpaceHomeomorph f g hA hB hC).symm
    (smallSpaceHomeomorph f g hA hB hC ((chartSystem f g).chart _ x))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- The original first leg, changed to each admissible original target chart. -/
def smallFstPullback (T : (smallPresentation f g hA hB hC).atlas.Index) (i : A.atlas.Index)
    (h : smallFstBase f g hA hB hC '' range ((smallPresentation f g hA hB hC).atlas.chart T) ⊆
      range (A.atlas.chart i)) :
    BoundedAlgHom K (A.atlas.algebra i) (algebra f g (smallRep f g hA hB hC T)) :=
  A.atlas.changeMapChart (smallRep f g hA hB hC T).val.1 i _ (leftMap f g _)
    (fun x => by simpa only [smallFstBase_chart] using h ⟨_, ⟨x, rfl⟩, rfl⟩)

/-- The original second leg, changed to each admissible original target chart. -/
def smallSndPullback (T : (smallPresentation f g hA hB hC).atlas.Index) (i : B.atlas.Index)
    (h : smallSndBase f g hA hB hC '' range ((smallPresentation f g hA hB hC).atlas.chart T) ⊆
      range (B.atlas.chart i)) :
    BoundedAlgHom K (B.atlas.algebra i) (algebra f g (smallRep f g hA hB hC T)) :=
  B.atlas.changeMapChart (smallRep f g hA hB hC T).val.2 i _ (rightMap f g _)
    (fun x => by simpa only [smallSndBase_chart] using h ⟨_, ⟨x, rfl⟩, rfl⟩)

/-- The first projection, retaining every admissible bounded pullback. -/
def smallFstHom : CompatibleStrongHom (smallPresentation f g hA hB hC) A where
  baseMap := smallFstBase f g hA hB hC
  target_exists T := ⟨(smallRep f g hA hB hC T).val.1, by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact (smallFstBase_chart f g hA hB hC T x).symm ▸ ⟨_, rfl⟩⟩
  pullback T i h := smallFstPullback f g hA hB hC T i h
  chart_comm T i h x := by
    change BanachSpectrum (algebra f g (smallRep f g hA hB hC T)) at x
    exact (A.atlas.changeMapChart_chart _ _ _ _ _ x).trans
      (smallFstBase_chart f g hA hB hC T x).symm
  restriction_comm T T' j j' hT hj h h' := by
    let p := smallRep f g hA hB hC T
    let p' := smallRep f g hA hB hC T'
    have hTT' := small_chart_subset f g hA hB hC T T' hT
    change (rangeRestriction f g hTT').comp (smallFstPullback f g hA hB hC T' j' h') =
      (smallFstPullback f g hA hB hC T j h).comp (A.atlas.restriction j j' hj)
    have hmem : ∀ x, A.atlas.chart p.val.1 (leftPoint f g p x) ∈ range (A.atlas.chart j) :=
      fun x => by simpa only [p, smallFstBase_chart] using h ⟨_, ⟨x, rfl⟩, rfl⟩
    have hmem' : ∀ x, A.atlas.chart p'.val.1 (leftPoint f g p' x) ∈ range (A.atlas.chart j') :=
      fun x => by simpa only [p', smallFstBase_chart] using h' ⟨_, ⟨x, rfl⟩, rfl⟩
    have e2 := isMapChartChange_rangeRestriction_left f g hTT' j' hmem'
    have e3 := (A.atlas.changeMapChart_isMapChartChange p.val.1 j _ (leftMap f g p) hmem).trans
      A.atlas hmem (A.atlas.isMapChartChange_comp_restriction j j' hj _ _)
    have himg : ∀ x, A.atlas.chart p.val.1 (leftPoint f g p x) ∈ range (A.atlas.chart j') :=
      fun x => hj (hmem x)
    exact (A.atlas.eq_changeMapChart _ _ _ _ himg _ e2).trans
      (A.atlas.eq_changeMapChart _ _ _ _ himg _ e3).symm
  compatible := by
    refine (StrongHom.hasLocallyCompatiblePullbacks_iff _).mpr ?_
    intro T j k hj hk
    exact A.atlas.isMapChartChange_changeMapChart _ _ _ _ _ _ _

/-- The second projection, retaining every admissible bounded pullback. -/
def smallSndHom : CompatibleStrongHom (smallPresentation f g hA hB hC) B where
  baseMap := smallSndBase f g hA hB hC
  target_exists T := ⟨(smallRep f g hA hB hC T).val.2, by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact (smallSndBase_chart f g hA hB hC T x).symm ▸ ⟨_, rfl⟩⟩
  pullback T i h := smallSndPullback f g hA hB hC T i h
  chart_comm T i h x := by
    change BanachSpectrum (algebra f g (smallRep f g hA hB hC T)) at x
    exact (B.atlas.changeMapChart_chart _ _ _ _ _ x).trans
      (smallSndBase_chart f g hA hB hC T x).symm
  restriction_comm T T' j j' hT hj h h' := by
    let p := smallRep f g hA hB hC T
    let p' := smallRep f g hA hB hC T'
    have hTT' := small_chart_subset f g hA hB hC T T' hT
    change (rangeRestriction f g hTT').comp (smallSndPullback f g hA hB hC T' j' h') =
      (smallSndPullback f g hA hB hC T j h).comp (B.atlas.restriction j j' hj)
    have hmem : ∀ x, B.atlas.chart p.val.2 (rightPoint f g p x) ∈ range (B.atlas.chart j) :=
      fun x => by simpa only [p, smallSndBase_chart] using h ⟨_, ⟨x, rfl⟩, rfl⟩
    have hmem' : ∀ x, B.atlas.chart p'.val.2 (rightPoint f g p' x) ∈ range (B.atlas.chart j') :=
      fun x => by simpa only [p', smallSndBase_chart] using h' ⟨_, ⟨x, rfl⟩, rfl⟩
    have e2 := isMapChartChange_rangeRestriction_right f g hTT' j' hmem'
    have e3 := (B.atlas.changeMapChart_isMapChartChange p.val.2 j _ (rightMap f g p) hmem).trans
      B.atlas hmem (B.atlas.isMapChartChange_comp_restriction j j' hj _ _)
    have himg : ∀ x, B.atlas.chart p.val.2 (rightPoint f g p x) ∈ range (B.atlas.chart j') :=
      fun x => hj (hmem x)
    exact (B.atlas.eq_changeMapChart _ _ _ _ himg _ e2).trans
      (B.atlas.eq_changeMapChart _ _ _ _ himg _ e3).symm
  compatible := by
    refine (StrongHom.hasLocallyCompatiblePullbacks_iff _).mpr ?_
    intro T j k hj hk
    exact B.atlas.isMapChartChange_changeMapChart _ _ _ _ _ _ _

end Langlands.Analytic.FibreProduct
