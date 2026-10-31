import Langlands.Geometry.Analytic.StrongAtlasMaps

/-! # All-admissible bounded atlas maps through directed target charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X]

/-- Every two original chart domains are contained in one original chart.
This asks for no chosen greatest chart and no additional affinoid domains. -/
def HasDirectedCharts (a : IndexedAffinoidAtlas.{u, v, w} K X) : Prop :=
  ∀ i j : a.Index, ∃ q : a.Index,
    Set.range (a.chart i) ⊆ Set.range (a.chart q) ∧
      Set.range (a.chart j) ⊆ Set.range (a.chart q)

theorem hasDirectedCharts_of_top (a : IndexedAffinoidAtlas.{u, v, w} K X)
    (t : a.Index)
    (ht : ∀ i, Set.range (a.chart i) ⊆ Set.range (a.chart t)) :
    a.HasDirectedCharts :=
  fun i j => ⟨t, ht i, ht j⟩

end Langlands.Analytic.IndexedAffinoidAtlas

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

namespace Hom

/-- The actual chosen pullback followed by restriction from a containing chart. -/
def pullbackToUpper (f : A ⟶ B) (i : A.atlas.Index) (q : B.atlas.Index)
    (hq : Set.range (B.atlas.chart (f.indexMap i)) ⊆ Set.range (B.atlas.chart q)) :
    BoundedAlgHom K (B.atlas.algebra q) (A.atlas.algebra i) :=
  (f.pullback i).comp (B.atlas.restriction (f.indexMap i) q hq)

theorem pullbackToUpper_chart (f : A ⟶ B) (i : A.atlas.Index) (q : B.atlas.Index)
    (hq : Set.range (B.atlas.chart (f.indexMap i)) ⊆ Set.range (B.atlas.chart q))
    (x : BanachSpectrum (A.atlas.algebra i)) :
    B.atlas.chart q (BanachSpectrum.comap (f.pullbackToUpper i q hq).toBoundedRingHom x) =
      f.baseMap (A.atlas.chart i x) := by
  change B.atlas.chart q
    (BanachSpectrum.comap (B.atlas.restriction (f.indexMap i) q hq).toBoundedRingHom
      (BanachSpectrum.comap (f.pullback i).toBoundedRingHom x)) = _
  rw [B.atlas.restriction_chart, f.chart_comm]

theorem pullbackToUpper_comp (f : A ⟶ B) (i : A.atlas.Index)
    (q r : B.atlas.Index)
    (hq : Set.range (B.atlas.chart (f.indexMap i)) ⊆ Set.range (B.atlas.chart q))
    (hqr : Set.range (B.atlas.chart q) ⊆ Set.range (B.atlas.chart r)) :
    (f.pullbackToUpper i q hq).comp (B.atlas.restriction q r hqr) =
      f.pullbackToUpper i r (hq.trans hqr) := by
  dsimp only [pullbackToUpper]
  rw [BoundedAlgHom.comp_assoc, ← B.atlas.restriction_comp]

/-- The actual domain universal property constructs the local factorization
inside any one upper chart. -/
theorem factorThroughUpper_existsUnique (f : A ⟶ B) (i : A.atlas.Index)
    (j q : B.atlas.Index)
    (hs : Set.range (B.atlas.chart (f.indexMap i)) ⊆ Set.range (B.atlas.chart q))
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart q))
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    ∃! ψ : BoundedAlgHom K (B.atlas.algebra j) (A.atlas.algebra i),
      ψ.comp (B.atlas.restriction j q hj) = f.pullbackToUpper i q hs := by
  apply B.atlas.restriction_universal j q hj (A.atlas.algebra i)
  intro x
  rw [f.pullbackToUpper_chart]
  exact h ⟨_, ⟨x, rfl⟩, rfl⟩

/-- Directedness proves independence of the upper chart, including all bounded
algebra data, rather than only the induced maps on spectrum points. -/
theorem directedPullback_existsUnique (f : A ⟶ B) (hd : B.atlas.HasDirectedCharts)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    ∃! ψ : BoundedAlgHom K (B.atlas.algebra j) (A.atlas.algebra i),
      ∀ (q : B.atlas.Index)
        (hs : Set.range (B.atlas.chart (f.indexMap i)) ⊆ Set.range (B.atlas.chart q))
        (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart q)),
        ψ.comp (B.atlas.restriction j q hj) = f.pullbackToUpper i q hs := by
  obtain ⟨q₀, hs₀, hj₀⟩ := hd (f.indexMap i) j
  obtain ⟨ψ, hψ, _⟩ := f.factorThroughUpper_existsUnique i j q₀ hs₀ hj₀ h
  refine ⟨ψ, ?_, ?_⟩
  · intro q hs hj
    obtain ⟨r, h₀r, hqr⟩ := hd q₀ q
    apply B.atlas.restriction_hom_ext q r hqr (A.atlas.algebra i)
    calc
      (ψ.comp (B.atlas.restriction j q hj)).comp (B.atlas.restriction q r hqr) =
          (ψ.comp (B.atlas.restriction j q₀ hj₀)).comp
            (B.atlas.restriction q₀ r h₀r) := by
        rw [BoundedAlgHom.comp_assoc,
          ← B.atlas.restriction_comp j q r hj hqr (hj.trans hqr),
          BoundedAlgHom.comp_assoc,
          ← B.atlas.restriction_comp j q₀ r hj₀ h₀r (hj₀.trans h₀r)]
      _ = f.pullbackToUpper i r (hs.trans hqr) := by
        rw [hψ, f.pullbackToUpper_comp]
      _ = (f.pullbackToUpper i q hs).comp (B.atlas.restriction q r hqr) :=
        (f.pullbackToUpper_comp i q r hs hqr).symm
  · intro χ hχ
    apply B.atlas.restriction_hom_ext j q₀ hj₀ (A.atlas.algebra i)
    exact (hχ q₀ hs₀ hj₀).trans hψ.symm

/-- Construct the unique actual bounded pullback at every admissible target. -/
def directedPullback (f : A ⟶ B) (hd : B.atlas.HasDirectedCharts)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    BoundedAlgHom K (B.atlas.algebra j) (A.atlas.algebra i) :=
  Classical.choose (f.directedPullback_existsUnique hd i j h).exists

theorem directedPullback_comp_restriction (f : A ⟶ B) (hd : B.atlas.HasDirectedCharts)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (q : B.atlas.Index)
    (hs : Set.range (B.atlas.chart (f.indexMap i)) ⊆ Set.range (B.atlas.chart q))
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart q)) :
    (f.directedPullback hd i j h).comp (B.atlas.restriction j q hj) =
      f.pullbackToUpper i q hs :=
  Classical.choose_spec (f.directedPullback_existsUnique hd i j h).exists q hs hj

theorem directedPullback_chart (f : A ⟶ B) (hd : B.atlas.HasDirectedCharts)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (x : BanachSpectrum (A.atlas.algebra i)) :
    B.atlas.chart j
        (BanachSpectrum.comap (f.directedPullback hd i j h).toBoundedRingHom x) =
      f.baseMap (A.atlas.chart i x) := by
  obtain ⟨q, hs, hj⟩ := hd (f.indexMap i) j
  rw [← f.pullbackToUpper_chart i q hs x,
    ← f.directedPullback_comp_restriction hd i j h q hs hj]
  exact (B.atlas.restriction_chart j q hj _).symm

theorem directedPullback_naturality (f : A ⟶ B) (hd : B.atlas.HasDirectedCharts)
    (i i' : A.atlas.Index) (j j' : B.atlas.Index)
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart j'))
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (h' : f.baseMap '' Set.range (A.atlas.chart i') ⊆ Set.range (B.atlas.chart j')) :
    (A.atlas.restriction i i' hi).comp (f.directedPullback hd i' j' h') =
      (f.directedPullback hd i j h).comp (B.atlas.restriction j j' hj) := by
  obtain ⟨q, hs, hjq⟩ := hd (f.indexMap i') j'
  have hsi := (f.index_mono i i' hi).trans hs
  have hjq' := hj.trans hjq
  apply B.atlas.restriction_hom_ext j' q hjq (A.atlas.algebra i)
  calc
    ((A.atlas.restriction i i' hi).comp (f.directedPullback hd i' j' h')).comp
        (B.atlas.restriction j' q hjq) =
        (A.atlas.restriction i i' hi).comp (f.pullbackToUpper i' q hs) := by
      rw [BoundedAlgHom.comp_assoc, f.directedPullback_comp_restriction]
    _ = f.pullbackToUpper i q hsi := by
      dsimp only [pullbackToUpper]
      rw [← BoundedAlgHom.comp_assoc, f.restriction_comm,
        BoundedAlgHom.comp_assoc, ← B.atlas.restriction_comp]
    _ = (f.directedPullback hd i j h).comp (B.atlas.restriction j q hjq') :=
      (f.directedPullback_comp_restriction hd i j h q hsi hjq').symm
    _ = ((f.directedPullback hd i j h).comp (B.atlas.restriction j j' hj)).comp
        (B.atlas.restriction j' q hjq) := by
      rw [BoundedAlgHom.comp_assoc, ← B.atlas.restriction_comp]

theorem directedPullback_selected (f : A ⟶ B) (hd : B.atlas.HasDirectedCharts)
    (i : A.atlas.Index) :
    f.directedPullback hd i (f.indexMap i) (f.image_chart_subset i) = f.pullback i := by
  obtain ⟨q, hs, hj⟩ := hd (f.indexMap i) (f.indexMap i)
  apply B.atlas.restriction_hom_ext (f.indexMap i) q hj (A.atlas.algebra i)
  exact f.directedPullback_comp_restriction hd i (f.indexMap i)
    (f.image_chart_subset i) q hs hj

end Hom

namespace StrongHom

/-- All-admissible strong data are constructed through directed original target
charts using actual domain factorization, with no output maps as inputs. -/
def ofDirected (f : A ⟶ B) (hd : B.atlas.HasDirectedCharts) : StrongHom A B where
  baseMap := f.baseMap
  target_exists i := ⟨f.indexMap i, f.image_chart_subset i⟩
  pullback := f.directedPullback hd
  chart_comm := f.directedPullback_chart hd
  restriction_comm := f.directedPullback_naturality hd

theorem ofDirected_pullback_selected (f : A ⟶ B) (hd : B.atlas.HasDirectedCharts)
    (i : A.atlas.Index) :
    (ofDirected f hd).pullback i (f.indexMap i) (f.image_chart_subset i) = f.pullback i :=
  f.directedPullback_selected hd i

/-- A strong extension with the original base map and selected bounded maps
is uniquely determined, including every admissible bounded pullback. -/
theorem eq_ofDirected_of_pullback_selected (f : A ⟶ B)
    (hd : B.atlas.HasDirectedCharts) (g : StrongHom A B)
    (hb : g.baseMap = f.baseMap)
    (hp : ∀ i, g.pullback i (f.indexMap i)
      (by rw [hb]; exact f.image_chart_subset i) = f.pullback i) :
    g = ofDirected f hd := by
  rcases g with ⟨gb, gt, gp, gc, gr⟩
  dsimp only at hb hp ⊢
  subst gb
  refine StrongHom.ext (f := ⟨f.baseMap, gt, gp, gc, gr⟩)
    (g := ofDirected f hd) rfl ?_
  apply heq_of_eq
  funext i j h
  change gp i j h = f.directedPullback hd i j h
  apply (f.directedPullback_existsUnique hd i j h).unique
    ?_ (f.directedPullback_comp_restriction hd i j h)
  intro q hs hj
  have hq := (f.image_chart_subset i).trans hs
  have h₁ := gr i i j q Subset.rfl hj h hq
  have h₂ := gr i i (f.indexMap i) q Subset.rfl hs (f.image_chart_subset i) hq
  simp only [A.atlas.restriction_id, BoundedAlgHom.id_comp] at h₁ h₂
  calc
    (gp i j h).comp (B.atlas.restriction j q hj) = gp i q hq := h₁.symm
    _ = (gp i (f.indexMap i) (f.image_chart_subset i)).comp
        (B.atlas.restriction (f.indexMap i) q hs) := h₂
    _ = f.pullbackToUpper i q hs := by rw [hp]; rfl

/-- The directed construction recovers the published greatest-chart
construction as an equality of the complete strong maps. -/
theorem ofDirected_eq_ofTopChart (f : A ⟶ B) (hd : B.atlas.HasDirectedCharts)
    (t : B.atlas.Index)
    (ht : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart t)) :
    ofDirected f hd = ofTopChart f t ht :=
  (eq_ofDirected_of_pullback_selected f hd (ofTopChart f t ht) rfl
    (ofTopChart_pullback_selected f t ht)).symm

end StrongHom

end Langlands.Analytic.AffinoidAtlasPresentation
