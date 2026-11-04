import Langlands.Geometry.Analytic.SaturatedStrongMapChartChange
import Langlands.Geometry.Analytic.DirectedAtlasComposition

/-! # Strong composition on atlases containing all local affinoid domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- Choose one admissible original target chart for each original source chart.
No monotonicity of these choices is required. -/
def chosenTargetIndex (f : StrongHom A B) (i : A.atlas.Index) : B.atlas.Index :=
  Classical.choose (f.target_exists i)

theorem chosenTarget_admissible (f : StrongHom A B) (i : A.atlas.Index) :
    f.baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (B.atlas.chart (f.chosenTargetIndex i)) :=
  Classical.choose_spec (f.target_exists i)

/-- Every admissible final target chart contains the entire spectrum image of
any admissible chain of the original bounded pullbacks. -/
theorem chainPullback_image_chart (f : StrongHom A B) (g : StrongHom B C)
    (i : A.atlas.Index) (j : B.atlas.Index) (p k : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart p))
    (h : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k))
    (x : BanachSpectrum (A.atlas.algebra i)) :
    C.atlas.chart p
        (BanachSpectrum.comap (f.chainPullback g i j p hf hg).toBoundedRingHom x) ∈
      Set.range (C.atlas.chart k) := by
  rw [f.chainPullback_chart g i j p hf hg]
  exact h ⟨A.atlas.chart i x, ⟨x, rfl⟩, rfl⟩

/-- Unrelated admissible chains obey the full universal target-chart-change
law when the first two atlases contain all their local affinoid domains. -/
theorem chainPullback_isMapChartChange (f : StrongHom A B) (g : StrongHom B C)
    (ha : A.atlas.HasAllLocalDomains) (hb : B.atlas.HasAllLocalDomains)
    (i : A.atlas.Index) (j j' : B.atlas.Index) (p p' : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hf' : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j'))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart p))
    (hg' : g.baseMap '' Set.range (B.atlas.chart j') ⊆ Set.range (C.atlas.chart p')) :
    C.atlas.IsMapChartChange p p' (A.atlas.algebra i)
      (f.chainPullback g i j p hf hg) (f.chainPullback g i j' p' hf' hg') :=
  g.mapAffinoidChart_isMapChartChange hb j j' p p' hg hg' (A.atlas.algebra i)
    (f.pullback i j hf) (f.pullback i j' hf')
    (f.pullback_image_chart i j j' hf hf')
    (f.pullback_isMapChartChange ha i j j' hf hf')

/-- Change the composite of two chosen bounded pullbacks to any admissible
final chart, using actual finite-cover bounded descent. -/
def saturatedCompPullback (f : StrongHom A B) (g : StrongHom B C)
    (i : A.atlas.Index) (k : C.atlas.Index)
    (h : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k)) :
    BoundedAlgHom K (C.atlas.algebra k) (A.atlas.algebra i) :=
  C.atlas.changeMapChart (g.chosenTargetIndex (f.chosenTargetIndex i)) k
    (A.atlas.algebra i)
    (f.chainPullback g i (f.chosenTargetIndex i)
      (g.chosenTargetIndex (f.chosenTargetIndex i))
      (f.chosenTarget_admissible i) (g.chosenTarget_admissible _))
    (f.chainPullback_image_chart g i _ _ k
      (f.chosenTarget_admissible i) (g.chosenTarget_admissible _) h)

theorem saturatedCompPullback_chart (f : StrongHom A B) (g : StrongHom B C)
    (i : A.atlas.Index) (k : C.atlas.Index)
    (h : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k))
    (x : BanachSpectrum (A.atlas.algebra i)) :
    C.atlas.chart k
        (BanachSpectrum.comap (f.saturatedCompPullback g i k h).toBoundedRingHom x) =
      g.baseMap (f.baseMap (A.atlas.chart i x)) := by
  unfold saturatedCompPullback
  rw [C.atlas.changeMapChart_chart, f.chainPullback_chart]

/-- The pullback is independent of both original chart choices: it can be
computed by changing any admissible chain to the requested final chart. -/
theorem saturatedCompPullback_eq_chainChange (f : StrongHom A B) (g : StrongHom B C)
    (ha : A.atlas.HasAllLocalDomains) (hb : B.atlas.HasAllLocalDomains)
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
  exact (f.chainPullback_isMapChartChange g ha hb i _ j _ p
    (f.chosenTarget_admissible i) hf (g.chosenTarget_admissible _) hg).trans C.atlas
      (f.chainPullback_image_chart g i _ _ p
        (f.chosenTarget_admissible i) (g.chosenTarget_admissible _)
        (f.comp_admissible g i j p hf hg))
      (C.atlas.changeMapChart_isMapChartChange p k (A.atlas.algebra i) _
        (f.chainPullback_image_chart g i j p k hf hg h))

/-- With a fixed target, the constructed bounded pullbacks commute with every
original source-chart restriction. -/
theorem saturatedCompPullback_source (f : StrongHom A B) (g : StrongHom B C)
    (ha : A.atlas.HasAllLocalDomains) (hb : B.atlas.HasAllLocalDomains)
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
    _ hrel).trans (f.saturatedCompPullback_eq_chainChange g ha hb i j p k hf hg h).symm

/-- With a fixed source, the constructed bounded pullbacks commute with every
original target-chart restriction. -/
theorem saturatedCompPullback_target (f : StrongHom A B) (g : StrongHom B C)
    (i : A.atlas.Index) (k k' : C.atlas.Index)
    (hk : Set.range (C.atlas.chart k) ⊆ Set.range (C.atlas.chart k'))
    (h : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k))
    (h' : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k')) :
    f.saturatedCompPullback g i k' h' =
      (f.saturatedCompPullback g i k h).comp (C.atlas.restriction k k' hk) := by
  let j := f.chosenTargetIndex i
  let p := g.chosenTargetIndex j
  let hf := f.chosenTarget_admissible i
  let hg := g.chosenTarget_admissible j
  have himage (x : BanachSpectrum (A.atlas.algebra i)) :
      C.atlas.chart k (BanachSpectrum.comap
        (f.saturatedCompPullback g i k h).toBoundedRingHom x) ∈
          Set.range (C.atlas.chart k') := by
    rw [f.saturatedCompPullback_chart g i k h]
    exact h' ⟨A.atlas.chart i x, ⟨x, rfl⟩, rfl⟩
  exact (C.atlas.changeMapChart_trans p k k' (A.atlas.algebra i)
    (f.chainPullback g i j p hf hg)
    (f.chainPullback_image_chart g i j p k hf hg h)
    (f.chainPullback_image_chart g i j p k' hf hg h') himage).symm.trans
      (C.atlas.changeMapChart_of_subset k k' hk (A.atlas.algebra i) _ himage)

/-- All source and target restriction equations hold for the actual family of
bounded pullbacks, without monotone choices, directedness or a greatest chart. -/
theorem saturatedCompPullback_naturality (f : StrongHom A B) (g : StrongHom B C)
    (ha : A.atlas.HasAllLocalDomains) (hb : B.atlas.HasAllLocalDomains)
    (i i' : A.atlas.Index) (k k' : C.atlas.Index)
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (hk : Set.range (C.atlas.chart k) ⊆ Set.range (C.atlas.chart k'))
    (h : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k))
    (h' : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i') ⊆
      Set.range (C.atlas.chart k')) :
    (A.atlas.restriction i i' hi).comp (f.saturatedCompPullback g i' k' h') =
      (f.saturatedCompPullback g i k h).comp (C.atlas.restriction k k' hk) :=
  (f.saturatedCompPullback_source g ha hb i i' k' hi (h.trans hk) h').trans
    (f.saturatedCompPullback_target g i k k' hk h (h.trans hk))

/-- Compose actual all-admissible-pair strong maps when the source and
intermediate atlases contain all local full affinoid domains. -/
def saturatedComp (f : StrongHom A B) (g : StrongHom B C)
    (ha : A.atlas.HasAllLocalDomains) (hb : B.atlas.HasAllLocalDomains) :
    StrongHom A C where
  baseMap := g.baseMap.comp f.baseMap
  target_exists i := ⟨g.chosenTargetIndex (f.chosenTargetIndex i),
    f.comp_admissible g i _ _ (f.chosenTarget_admissible i)
      (g.chosenTarget_admissible _)⟩
  pullback := f.saturatedCompPullback g
  chart_comm := f.saturatedCompPullback_chart g
  restriction_comm := f.saturatedCompPullback_naturality g ha hb

@[simp]
theorem saturatedComp_baseMap (f : StrongHom A B) (g : StrongHom B C)
    (ha : A.atlas.HasAllLocalDomains) (hb : B.atlas.HasAllLocalDomains) :
    (f.saturatedComp g ha hb).baseMap = g.baseMap.comp f.baseMap := rfl

/-- The full constructed strong map recovers the literal bounded composite on
every admissible original chart chain, including unrelated choices. -/
theorem saturatedComp_pullback (f : StrongHom A B) (g : StrongHom B C)
    (ha : A.atlas.HasAllLocalDomains) (hb : B.atlas.HasAllLocalDomains)
    (i : A.atlas.Index) (j : B.atlas.Index) (k : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart k))
    (h : (f.saturatedComp g ha hb).baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k)) :
    (f.saturatedComp g ha hb).pullback i k h = f.chainPullback g i j k hf hg :=
  (f.saturatedCompPullback_eq_chainChange g ha hb i j k k hf hg h).trans
    (C.atlas.changeMapChart_self k (A.atlas.algebra i) _ _)

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
