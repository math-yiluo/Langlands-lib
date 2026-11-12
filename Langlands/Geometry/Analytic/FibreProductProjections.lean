import Langlands.Geometry.Analytic.FibreProductAtlas
import Langlands.Geometry.Analytic.CompatibleStrongCategory

/-! # The projections of a fibre product as compatible strong maps -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- A map followed by a restriction is its own chart change. -/
theorem isMapChartChange_comp_restriction (j j' : a.Index)
    (hj : Set.range (a.chart j) ⊆ Set.range (a.chart j'))
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (a.algebra j) R) :
    a.IsMapChartChange j j' R φ (φ.comp (a.restriction j j' hj)) := by
  have h := a.changeMapChart_isMapChartChange j j' R φ (fun x => hj ⟨_, rfl⟩)
  rwa [a.changeMapChart_of_subset j j' hj] at h

/-- Two chart changes of one map are chart changes of each other. -/
theorem isMapChartChange_changeMapChart (r j k : a.Index) (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra r) R)
    (hj : ∀ x : BanachSpectrum R,
      a.chart r (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j))
    (hk : ∀ x : BanachSpectrum R,
      a.chart r (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart k)) :
    a.IsMapChartChange j k R (a.changeMapChart r j R φ hj) (a.changeMapChart r k R φ hk) :=
  (a.changeMapChart_reverse_isMapChartChange r j R φ hj).trans a
    (a.changeMapChart_image_original r j R φ hj) (a.changeMapChart_isMapChartChange r k R φ hk)

end IndexedAffinoidAtlas

namespace FibreProduct

open AffinoidAtlasPresentation

variable {A B C : AffinoidAtlasPresentation.{u, u, u} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)
  [T2Space A.space] [T2Space B.space] [T2Space C.space]
  (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)

/-! ## The first projection -/

/-- The pullback along the first projection, from a chart of `X` containing the image of a
fibre product chart: the first leg, changed to that chart. -/
def fstPullback (T : AtlasIndex f g) (i : A.atlas.Index)
    (h : fst f g '' range ((chartSystem f g).chart T.rep) ⊆ range (A.atlas.chart i)) :
    BoundedAlgHom K (A.atlas.algebra i) (algebra f g T.rep) :=
  A.atlas.changeMapChart T.rep.1.1 i (algebra f g T.rep) (leftMap f g T.rep)
    (fun x => h ⟨_, ⟨x, rfl⟩, rfl⟩)

/-- The first projection `X ×_S Y → X` as a compatible strong map. -/
def fstHom : CompatibleStrongHom (presentation f g hA hB) A where
  baseMap := ⟨fst f g, continuous_fst f g⟩
  target_exists T := ⟨T.rep.1.1, by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨_, rfl⟩⟩
  pullback T i h := fstPullback f g T i h
  chart_comm T i h x := A.atlas.changeMapChart_chart _ _ _ _ _ x
  restriction_comm T T' j j' hT hj h h' := by
    let r := T.rep.1.1
    have e2 := isMapChartChange_rangeRestriction_left f g (p := T.rep) (q := T'.rep) hT j'
      (fun x => h' ⟨_, ⟨x, rfl⟩, rfl⟩)
    have e3 := (A.atlas.changeMapChart_isMapChartChange r j (algebra f g T.rep)
      (leftMap f g T.rep) (fun x => h ⟨_, ⟨x, rfl⟩, rfl⟩)).trans A.atlas
        (fun x => h ⟨_, ⟨x, rfl⟩, rfl⟩)
        (A.atlas.isMapChartChange_comp_restriction j j' hj _ _)
    have himg : ∀ x : BanachSpectrum (algebra f g T.rep),
        A.atlas.chart r (leftPoint f g T.rep x) ∈ range (A.atlas.chart j') :=
      fun x => hj (h ⟨_, ⟨x, rfl⟩, rfl⟩)
    exact (A.atlas.eq_changeMapChart _ _ _ _ himg _ e2).trans
      (A.atlas.eq_changeMapChart _ _ _ _ himg _ e3).symm
  compatible := by
    refine (StrongHom.hasLocallyCompatiblePullbacks_iff _).2 ?_
    intro T j k hj hk
    exact A.atlas.isMapChartChange_changeMapChart _ _ _ _ _ _ _

/-! ## The second projection -/

/-- The pullback along the second projection. -/
def sndPullback (T : AtlasIndex f g) (j : B.atlas.Index)
    (h : snd f g '' range ((chartSystem f g).chart T.rep) ⊆ range (B.atlas.chart j)) :
    BoundedAlgHom K (B.atlas.algebra j) (algebra f g T.rep) :=
  B.atlas.changeMapChart T.rep.1.2 j (algebra f g T.rep) (rightMap f g T.rep)
    (fun x => h ⟨_, ⟨x, rfl⟩, rfl⟩)

/-- The second projection `X ×_S Y → Y` as a compatible strong map. -/
def sndHom : CompatibleStrongHom (presentation f g hA hB) B where
  baseMap := ⟨snd f g, continuous_snd f g⟩
  target_exists T := ⟨T.rep.1.2, by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨_, rfl⟩⟩
  pullback T j h := sndPullback f g T j h
  chart_comm T j h x := B.atlas.changeMapChart_chart _ _ _ _ _ x
  restriction_comm T T' j j' hT hj h h' := by
    let r := T.rep.1.2
    have e2 := isMapChartChange_rangeRestriction_right f g (p := T.rep) (q := T'.rep) hT j'
      (fun x => h' ⟨_, ⟨x, rfl⟩, rfl⟩)
    have e3 := (B.atlas.changeMapChart_isMapChartChange r j (algebra f g T.rep)
      (rightMap f g T.rep) (fun x => h ⟨_, ⟨x, rfl⟩, rfl⟩)).trans B.atlas
        (fun x => h ⟨_, ⟨x, rfl⟩, rfl⟩)
        (B.atlas.isMapChartChange_comp_restriction j j' hj _ _)
    have himg : ∀ x : BanachSpectrum (algebra f g T.rep),
        B.atlas.chart r (rightPoint f g T.rep x) ∈ range (B.atlas.chart j') :=
      fun x => hj (h ⟨_, ⟨x, rfl⟩, rfl⟩)
    exact (B.atlas.eq_changeMapChart _ _ _ _ himg _ e2).trans
      (B.atlas.eq_changeMapChart _ _ _ _ himg _ e3).symm
  compatible := by
    refine (StrongHom.hasLocallyCompatiblePullbacks_iff _).2 ?_
    intro T j k hj hk
    exact B.atlas.isMapChartChange_changeMapChart _ _ _ _ _ _ _

/-! ## The commutative square -/

/-- The square `fst ≫ f = snd ≫ g` of compatible strong maps. -/
theorem fstHom_comp : (fstHom f g hA hB).comp f = (sndHom f g hA hB).comp g := by
  refine CompatibleStrongHom.ext_of_pullback (ContinuousMap.ext fun z => baseMap_fst f g z)
    fun T => ?_
  let p := T.rep
  have h₁ : (fstHom f g hA hB).baseMap '' range ((presentation f g hA hB).atlas.chart T) ⊆
      range (A.atlas.chart p.1.1) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨_, rfl⟩
  have h₂ : (sndHom f g hA hB).baseMap '' range ((presentation f g hA hB).atlas.chart T) ⊆
      range (B.atlas.chart p.1.2) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨_, rfl⟩
  have hk : ((fstHom f g hA hB).comp f).baseMap '' range ((presentation f g hA hB).atlas.chart T) ⊆
      range (C.atlas.chart (base f g p)) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact (isCommonBase_base f g p).1 ⟨_, ⟨_, rfl⟩, rfl⟩
  refine ⟨base f g p, hk, ?_⟩
  have el := CompatibleStrongHom.comp_pullback (fstHom f g hA hB) f T p.1.1 (base f g p) h₁
    (isCommonBase_base f g p).1 hk
  have er := CompatibleStrongHom.comp_pullback (sndHom f g hA hB) g T p.1.2 (base f g p) h₂
    (isCommonBase_base f g p).2 (by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact (isCommonBase_base f g p).2 ⟨_, ⟨_, rfl⟩, rfl⟩)
  refine el.trans (Eq.trans ?_ er.symm)
  change (fstPullback f g T p.1.1 h₁).comp (leftBase f g p) =
    (sndPullback f g T p.1.2 h₂).comp (rightBase f g p)
  unfold fstPullback sndPullback
  rw [A.atlas.changeMapChart_self, B.atlas.changeMapChart_self]
  exact AffinoidPushout.condition (leftBase f g p) (rightBase f g p)

end FibreProduct

end Langlands.Analytic
