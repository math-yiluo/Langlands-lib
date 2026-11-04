import Langlands.Geometry.Analytic.CompatibleStrongMaps
import Langlands.Geometry.Analytic.SaturatedStrongComposition

/-! # Composition of the actual original compatible strong-map families -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- Any two admissible original chains agree by the original families'
intrinsic coherence and preservation of arbitrary bounded chart changes. -/
theorem chainPullback_isMapChartChange_of_coherent (f : StrongHom A B) (g : StrongHom B C)
    (hfc : f.HasCoherentPullbacks) (hgc : g.HasCoherentPullbacks)
    (i : A.atlas.Index) (j j' : B.atlas.Index) (p p' : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hf' : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j'))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart p))
    (hg' : g.baseMap '' Set.range (B.atlas.chart j') ⊆ Set.range (C.atlas.chart p')) :
    C.atlas.IsMapChartChange p p' (A.atlas.algebra i)
      (f.chainPullback g i j p hf hg) (f.chainPullback g i j' p' hf' hg') :=
  g.mapAffinoidChart_isMapChartChange_of_coherent hgc j j' p p' hg hg' (A.atlas.algebra i)
    (f.pullback i j hf) (f.pullback i j' hf')
    (f.pullback_image_chart i j j' hf hf')
    (hfc i j j' hf hf')

/-- The existing bounded composite is independent of both original choices,
without requiring either original atlas to contain all local domains. -/
theorem saturatedCompPullback_eq_chainChange_of_coherent (f : StrongHom A B) (g : StrongHom B C)
    (hfc : f.HasCoherentPullbacks) (hgc : g.HasCoherentPullbacks)
    (i : A.atlas.Index) (j : B.atlas.Index) (p k : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart p))
    (h : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k)) :
    f.saturatedCompPullback g i k h =
      C.atlas.changeMapChart p k (A.atlas.algebra i)
        (f.chainPullback g i j p hf hg)
        (f.chainPullback_image_chart g i j p k hf hg h) := by
  symm
  apply C.atlas.eq_changeMapChart
  exact (f.chainPullback_isMapChartChange_of_coherent g hfc hgc i _ j _ p
    (f.chosenTarget_admissible i) hf (g.chosenTarget_admissible _) hg).trans C.atlas
      (f.chainPullback_image_chart g i _ _ p
        (f.chosenTarget_admissible i) (g.chosenTarget_admissible _)
        (f.comp_admissible g i j p hf hg))
      (C.atlas.changeMapChart_isMapChartChange p k (A.atlas.algebra i) _
        (f.chainPullback_image_chart g i j p k hf hg h))

/-- Every original source restriction commutes with the constructed composite. -/
theorem saturatedCompPullback_source_of_coherent (f : StrongHom A B) (g : StrongHom B C)
    (hfc : f.HasCoherentPullbacks) (hgc : g.HasCoherentPullbacks)
    (i i' : A.atlas.Index) (k : C.atlas.Index)
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (h : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k))
    (h' : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i') ⊆
      Set.range (C.atlas.chart k)) :
    (A.atlas.restriction i i' hi).comp (f.saturatedCompPullback g i' k h') =
      f.saturatedCompPullback g i k h := by
  let j := f.chosenTargetIndex i'
  let p := g.chosenTargetIndex j
  let hf' := f.chosenTarget_admissible i'
  let hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j) :=
    (Set.image_mono hi).trans hf'
  let hg := g.chosenTarget_admissible j
  have hρ :
      (A.atlas.restriction i i' hi).comp (f.chainPullback g i' j p hf' hg) =
        f.chainPullback g i j p hf hg :=
    congrArg (fun q : BoundedAlgHom K (B.atlas.algebra j) (A.atlas.algebra i) =>
      q.comp (g.pullback j p hg)) (f.restriction_comp_pullback i i' j hi hf hf')
  have hrel := (C.atlas.changeMapChart_isMapChartChange p k (A.atlas.algebra i')
    (f.chainPullback g i' j p hf' hg)
    (f.chainPullback_image_chart g i' j p k hf' hg h')).comp C.atlas
      (A.atlas.restriction i i' hi)
  rw [hρ] at hrel
  exact (C.atlas.eq_changeMapChart p k (A.atlas.algebra i)
    (f.chainPullback g i j p hf hg) (f.chainPullback_image_chart g i j p k hf hg h)
    _ hrel).trans (f.saturatedCompPullback_eq_chainChange_of_coherent g hfc hgc i j p k hf hg h).symm

/-- Complete two-variable naturality uses original-family coherence. -/
theorem saturatedCompPullback_naturality_of_coherent (f : StrongHom A B) (g : StrongHom B C)
    (hfc : f.HasCoherentPullbacks) (hgc : g.HasCoherentPullbacks)
    (i i' : A.atlas.Index) (k k' : C.atlas.Index)
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (hk : Set.range (C.atlas.chart k) ⊆ Set.range (C.atlas.chart k'))
    (h : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k))
    (h' : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i') ⊆
      Set.range (C.atlas.chart k')) :
    (A.atlas.restriction i i' hi).comp (f.saturatedCompPullback g i' k' h') =
      (f.saturatedCompPullback g i k h).comp (C.atlas.restriction k k' hk) :=
  (f.saturatedCompPullback_source_of_coherent g hfc hgc i i' k' hi (h.trans hk) h').trans
    (f.saturatedCompPullback_target g i k k' hk h (h.trans hk))

/-- The actual bounded composites at any two final target charts are related
by the constructed change of chart, even before source naturality is imposed. -/
theorem saturatedCompPullback_change (f : StrongHom A B) (g : StrongHom B C)
    (i : A.atlas.Index) (k k' : C.atlas.Index)
    (h : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k))
    (h' : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k'))
    (hk : ∀ x : BanachSpectrum (A.atlas.algebra i),
      C.atlas.chart k
        (BanachSpectrum.comap (f.saturatedCompPullback g i k h).toBoundedRingHom x) ∈
          Set.range (C.atlas.chart k')) :
    C.atlas.changeMapChart k k' (A.atlas.algebra i)
      (f.saturatedCompPullback g i k h) hk = f.saturatedCompPullback g i k' h' :=
  C.atlas.changeMapChart_trans _ k k' (A.atlas.algebra i) _
    (f.chainPullback_image_chart g i _ _ k
      (f.chosenTarget_admissible i) (g.chosenTarget_admissible _) h)
    (f.chainPullback_image_chart g i _ _ k'
      (f.chosenTarget_admissible i) (g.chosenTarget_admissible _) h') hk

/-- The constructed composite family satisfies the full coefficient-test law. -/
theorem saturatedCompPullback_isMapChartChange (f : StrongHom A B) (g : StrongHom B C)
    (i : A.atlas.Index) (k k' : C.atlas.Index)
    (h : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k))
    (h' : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k')) :
    C.atlas.IsMapChartChange k k' (A.atlas.algebra i)
      (f.saturatedCompPullback g i k h) (f.saturatedCompPullback g i k' h') := by
  have hk (x : BanachSpectrum (A.atlas.algebra i)) :
      C.atlas.chart k
        (BanachSpectrum.comap (f.saturatedCompPullback g i k h).toBoundedRingHom x) ∈
          Set.range (C.atlas.chart k') := by
    rw [f.saturatedCompPullback_chart]
    exact h' ⟨A.atlas.chart i x, ⟨x, rfl⟩, rfl⟩
  rw [← f.saturatedCompPullback_change g i k k' h h' hk]
  exact C.atlas.changeMapChart_isMapChartChange k k' (A.atlas.algebra i) _ hk

/-- Compose the actual original strong-map data under laws only on their
original bounded families. No extension or composition output is assumed. -/
def coherentComp (f : StrongHom A B) (g : StrongHom B C)
    (hfc : f.HasCoherentPullbacks) (hgc : g.HasCoherentPullbacks) :
    StrongHom A C where
  baseMap := g.baseMap.comp f.baseMap
  target_exists i := ⟨g.chosenTargetIndex (f.chosenTargetIndex i),
    f.comp_admissible g i _ _ (f.chosenTarget_admissible i)
      (g.chosenTarget_admissible _)⟩
  pullback := f.saturatedCompPullback g
  chart_comm := f.saturatedCompPullback_chart g
  restriction_comm := f.saturatedCompPullback_naturality_of_coherent g hfc hgc

@[simp]
theorem coherentComp_baseMap (f : StrongHom A B) (g : StrongHom B C)
    (hfc : f.HasCoherentPullbacks) (hgc : g.HasCoherentPullbacks) :
    (f.coherentComp g hfc hgc).baseMap = g.baseMap.comp f.baseMap := rfl

/-- Recover the literal bounded composite on every admissible original chain. -/
theorem coherentComp_pullback (f : StrongHom A B) (g : StrongHom B C)
    (hfc : f.HasCoherentPullbacks) (hgc : g.HasCoherentPullbacks)
    (i : A.atlas.Index) (j : B.atlas.Index) (k : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart k))
    (h : (f.coherentComp g hfc hgc).baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k)) :
    (f.coherentComp g hfc hgc).pullback i k h = f.chainPullback g i j k hf hg :=
  (f.saturatedCompPullback_eq_chainChange_of_coherent g hfc hgc i j k k hf hg h).trans
    (C.atlas.changeMapChart_self k (A.atlas.algebra i) _ _)

/-- Original-family coherence is closed under the constructed composition. -/
theorem hasCoherentPullbacks_coherentComp (f : StrongHom A B) (g : StrongHom B C)
    (hfc : f.HasCoherentPullbacks) (hgc : g.HasCoherentPullbacks) :
    (f.coherentComp g hfc hgc).HasCoherentPullbacks :=
  f.saturatedCompPullback_isMapChartChange g

/-- On saturated sources and intermediates this is the existing composition
as an entire strong map, including every original bounded pullback. -/
theorem coherentComp_eq_saturatedComp (f : StrongHom A B) (g : StrongHom B C)
    (hfc : f.HasCoherentPullbacks) (hgc : g.HasCoherentPullbacks)
    (ha : A.atlas.HasAllLocalDomains) (hb : B.atlas.HasAllLocalDomains) :
    f.coherentComp g hfc hgc = f.saturatedComp g ha hb := rfl

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

namespace Langlands.Analytic.AffinoidAtlasPresentation.CompatibleStrongHom

open Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- Actual compatible strong composition with its original local-domain law. -/
def comp (f : CompatibleStrongHom A B) (g : CompatibleStrongHom B C) :
    CompatibleStrongHom A C where
  toStrongHom := f.toStrongHom.coherentComp g.toStrongHom f.coherent g.coherent
  compatible := StrongHom.hasLocallyCompatiblePullbacks_iff _ |>.mpr
    (f.toStrongHom.hasCoherentPullbacks_coherentComp g.toStrongHom f.coherent g.coherent)

@[simp]
theorem comp_toStrongHom (f : CompatibleStrongHom A B) (g : CompatibleStrongHom B C) :
    (f.comp g).toStrongHom = f.toStrongHom.coherentComp g.toStrongHom f.coherent g.coherent :=
  rfl

@[simp]
theorem comp_baseMap (f : CompatibleStrongHom A B) (g : CompatibleStrongHom B C) :
    (f.comp g).baseMap = g.baseMap.comp f.baseMap := rfl

/-- Each admissible chain computes the full bounded pullback of the
compatible composite, without a containing intermediate choice condition. -/
theorem comp_pullback (f : CompatibleStrongHom A B) (g : CompatibleStrongHom B C)
    (i : A.atlas.Index) (j : B.atlas.Index) (k : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart k))
    (h : (f.comp g).baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k)) :
    (f.comp g).pullback i k h =
      (f.pullback i j hf).comp (g.pullback j k hg) :=
  f.toStrongHom.coherentComp_pullback g.toStrongHom f.coherent g.coherent i j k hf hg h

theorem comp_eq_saturatedComp (f : CompatibleStrongHom A B) (g : CompatibleStrongHom B C)
    (ha : A.atlas.HasAllLocalDomains) (hb : B.atlas.HasAllLocalDomains) :
    (f.comp g).toStrongHom = f.toStrongHom.saturatedComp g.toStrongHom ha hb := rfl

end Langlands.Analytic.AffinoidAtlasPresentation.CompatibleStrongHom
