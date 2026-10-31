import Langlands.Geometry.Analytic.DirectedAtlasMaps
import Langlands.Geometry.Analytic.StrongAtlasComposition

/-! # Strong composition through directed original atlas charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C D : AffinoidAtlasPresentation.{u, v, w} K}

/-- An admissible chain gives an admissible pair for the composite point map. -/
theorem comp_admissible (f : StrongHom A B) (g : StrongHom B C)
    (i : A.atlas.Index) (j : B.atlas.Index) (k : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart k)) :
    (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k) := by
  rintro _ ⟨x, hx, rfl⟩
  exact hg ⟨f.baseMap x, hf ⟨x, hx, rfl⟩, rfl⟩

/-- The actual bounded composite on any admissible chain of original charts. -/
def chainPullback (f : StrongHom A B) (g : StrongHom B C)
    (i : A.atlas.Index) (j : B.atlas.Index) (k : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart k)) :
    BoundedAlgHom K (C.atlas.algebra k) (A.atlas.algebra i) :=
  (f.pullback i j hf).comp (g.pullback j k hg)

theorem chainPullback_chart (f : StrongHom A B) (g : StrongHom B C)
    (i : A.atlas.Index) (j : B.atlas.Index) (k : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart k))
    (x : BanachSpectrum (A.atlas.algebra i)) :
    C.atlas.chart k
        (BanachSpectrum.comap (f.chainPullback g i j k hf hg).toBoundedRingHom x) =
      g.baseMap (f.baseMap (A.atlas.chart i x)) := by
  change C.atlas.chart k (BanachSpectrum.comap (g.pullback j k hg).toBoundedRingHom
    (BanachSpectrum.comap (f.pullback i j hf).toBoundedRingHom x)) = _
  rw [g.chart_comm, f.chart_comm]

/-- Chain pullbacks commute with all three actual atlas restrictions. -/
theorem chainPullback_naturality (f : StrongHom A B) (g : StrongHom B C)
    (i i' : A.atlas.Index) (j j' : B.atlas.Index) (k k' : C.atlas.Index)
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart j'))
    (hk : Set.range (C.atlas.chart k) ⊆ Set.range (C.atlas.chart k'))
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hf' : f.baseMap '' Set.range (A.atlas.chart i') ⊆ Set.range (B.atlas.chart j'))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart k))
    (hg' : g.baseMap '' Set.range (B.atlas.chart j') ⊆ Set.range (C.atlas.chart k')) :
    (A.atlas.restriction i i' hi).comp (f.chainPullback g i' j' k' hf' hg') =
      (f.chainPullback g i j k hf hg).comp (C.atlas.restriction k k' hk) := by
  dsimp only [chainPullback]
  rw [← BoundedAlgHom.comp_assoc, f.restriction_comm i i' j j' hi hj hf hf',
    BoundedAlgHom.comp_assoc, g.restriction_comm j j' k k' hj hk hg hg',
    ← BoundedAlgHom.comp_assoc]

/-- Two unrelated admissible chains become equal as bounded maps in an
actual common upper target chart. -/
theorem chainPullback_commonUpper (f : StrongHom A B) (g : StrongHom B C)
    (hb : B.atlas.HasDirectedCharts) (hc : C.atlas.HasDirectedCharts)
    (i : A.atlas.Index) (j j' : B.atlas.Index) (q q' : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hf' : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j'))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart q))
    (hg' : g.baseMap '' Set.range (B.atlas.chart j') ⊆ Set.range (C.atlas.chart q')) :
    ∃ (r : C.atlas.Index)
      (hqr : Set.range (C.atlas.chart q) ⊆ Set.range (C.atlas.chart r))
      (hq'r : Set.range (C.atlas.chart q') ⊆ Set.range (C.atlas.chart r)),
      (f.chainPullback g i j q hf hg).comp (C.atlas.restriction q r hqr) =
        (f.chainPullback g i j' q' hf' hg').comp (C.atlas.restriction q' r hq'r) := by
  obtain ⟨b, hjb, hj'b⟩ := hb j j'
  obtain ⟨p, hp⟩ := g.target_exists b
  obtain ⟨s, hqs, hq's⟩ := hc q q'
  obtain ⟨r, hsr, hpr⟩ := hc s p
  have hfb := hf.trans hjb
  have hgr := hp.trans hpr
  have H := f.chainPullback_naturality g i i j b q r Subset.rfl hjb
    (hqs.trans hsr) hf hfb hg hgr
  have H' := f.chainPullback_naturality g i i j' b q' r Subset.rfl hj'b
    (hq's.trans hsr) hf' hfb hg' hgr
  simp only [A.atlas.restriction_id, BoundedAlgHom.id_comp] at H H'
  exact ⟨r, hqs.trans hsr, hq's.trans hsr, H.symm.trans H'⟩

/-- Domain factorization constructs a bounded pullback at every admissible
final chart, with its equation at every possible containing chain. -/
theorem compPullback_existsUnique (f : StrongHom A B) (g : StrongHom B C)
    (hb : B.atlas.HasDirectedCharts) (hc : C.atlas.HasDirectedCharts)
    (i : A.atlas.Index) (k : C.atlas.Index)
    (h : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k)) :
    ∃! ψ : BoundedAlgHom K (C.atlas.algebra k) (A.atlas.algebra i),
      ∀ (j : B.atlas.Index) (q : C.atlas.Index)
        (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
        (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart q))
        (hk : Set.range (C.atlas.chart k) ⊆ Set.range (C.atlas.chart q)),
        ψ.comp (C.atlas.restriction k q hk) = f.chainPullback g i j q hf hg := by
  obtain ⟨j₀, hf₀⟩ := f.target_exists i
  obtain ⟨q₀, hg₀⟩ := g.target_exists j₀
  obtain ⟨q₁, h₀₁, hk₁⟩ := hc q₀ k
  have hg₁ := hg₀.trans h₀₁
  have hφ : ∀ x : BanachSpectrum (A.atlas.algebra i),
      C.atlas.chart q₁
        (BanachSpectrum.comap (f.chainPullback g i j₀ q₁ hf₀ hg₁).toBoundedRingHom x) ∈
          Set.range (C.atlas.chart k) := by
    intro x
    rw [f.chainPullback_chart]
    exact h ⟨_, ⟨x, rfl⟩, rfl⟩
  obtain ⟨ψ, hψ, _⟩ := C.atlas.restriction_universal k q₁ hk₁ (A.atlas.algebra i)
    (f.chainPullback g i j₀ q₁ hf₀ hg₁) hφ
  refine ⟨ψ, ?_, ?_⟩
  · intro j q hf hg hk
    obtain ⟨r, h₁r, hqr, heq⟩ :=
      f.chainPullback_commonUpper g hb hc i j₀ j q₁ q hf₀ hf hg₁ hg
    apply C.atlas.restriction_hom_ext q r hqr (A.atlas.algebra i)
    calc
      (ψ.comp (C.atlas.restriction k q hk)).comp (C.atlas.restriction q r hqr) =
          (ψ.comp (C.atlas.restriction k q₁ hk₁)).comp
            (C.atlas.restriction q₁ r h₁r) := by
        rw [BoundedAlgHom.comp_assoc,
          ← C.atlas.restriction_comp k q r hk hqr (hk.trans hqr),
          BoundedAlgHom.comp_assoc,
          ← C.atlas.restriction_comp k q₁ r hk₁ h₁r (hk₁.trans h₁r)]
      _ = (f.chainPullback g i j q hf hg).comp (C.atlas.restriction q r hqr) := by
        rw [hψ]
        exact heq
  · intro χ hχ
    apply C.atlas.restriction_hom_ext k q₁ hk₁ (A.atlas.algebra i)
    exact (hχ j₀ q₁ hf₀ hg₁ hk₁).trans hψ.symm

/-- The uniquely constructed bounded pullback for the composite. -/
def compPullback (f : StrongHom A B) (g : StrongHom B C)
    (hb : B.atlas.HasDirectedCharts) (hc : C.atlas.HasDirectedCharts)
    (i : A.atlas.Index) (k : C.atlas.Index)
    (h : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k)) :
    BoundedAlgHom K (C.atlas.algebra k) (A.atlas.algebra i) :=
  Classical.choose (f.compPullback_existsUnique g hb hc i k h).exists

theorem compPullback_comp_restriction (f : StrongHom A B) (g : StrongHom B C)
    (hb : B.atlas.HasDirectedCharts) (hc : C.atlas.HasDirectedCharts)
    (i : A.atlas.Index) (k : C.atlas.Index)
    (h : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k))
    (j : B.atlas.Index) (q : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart q))
    (hk : Set.range (C.atlas.chart k) ⊆ Set.range (C.atlas.chart q)) :
    (f.compPullback g hb hc i k h).comp (C.atlas.restriction k q hk) =
      f.chainPullback g i j q hf hg :=
  Classical.choose_spec (f.compPullback_existsUnique g hb hc i k h).exists j q hf hg hk

theorem compPullback_chart (f : StrongHom A B) (g : StrongHom B C)
    (hb : B.atlas.HasDirectedCharts) (hc : C.atlas.HasDirectedCharts)
    (i : A.atlas.Index) (k : C.atlas.Index)
    (h : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k))
    (x : BanachSpectrum (A.atlas.algebra i)) :
    C.atlas.chart k
        (BanachSpectrum.comap (f.compPullback g hb hc i k h).toBoundedRingHom x) =
      g.baseMap (f.baseMap (A.atlas.chart i x)) := by
  obtain ⟨j, hf⟩ := f.target_exists i
  obtain ⟨q₀, hg₀⟩ := g.target_exists j
  obtain ⟨q, h₀q, hkq⟩ := hc q₀ k
  rw [← f.chainPullback_chart g i j q hf (hg₀.trans h₀q) x,
    ← f.compPullback_comp_restriction g hb hc i k h j q hf (hg₀.trans h₀q) hkq]
  exact (C.atlas.restriction_chart k q hkq _).symm

theorem compPullback_naturality (f : StrongHom A B) (g : StrongHom B C)
    (hb : B.atlas.HasDirectedCharts) (hc : C.atlas.HasDirectedCharts)
    (i i' : A.atlas.Index) (k k' : C.atlas.Index)
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (hk : Set.range (C.atlas.chart k) ⊆ Set.range (C.atlas.chart k'))
    (h : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k))
    (h' : (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i') ⊆
      Set.range (C.atlas.chart k')) :
    (A.atlas.restriction i i' hi).comp (f.compPullback g hb hc i' k' h') =
      (f.compPullback g hb hc i k h).comp (C.atlas.restriction k k' hk) := by
  obtain ⟨j, hf'⟩ := f.target_exists i'
  obtain ⟨q₀, hg₀⟩ := g.target_exists j
  obtain ⟨q, h₀q, hk'q⟩ := hc q₀ k'
  have hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j) :=
    (Set.image_mono hi).trans hf'
  have hg := hg₀.trans h₀q
  have hkq := hk.trans hk'q
  apply C.atlas.restriction_hom_ext k' q hk'q (A.atlas.algebra i)
  calc
    ((A.atlas.restriction i i' hi).comp (f.compPullback g hb hc i' k' h')).comp
        (C.atlas.restriction k' q hk'q) =
        (A.atlas.restriction i i' hi).comp (f.chainPullback g i' j q hf' hg) := by
      rw [BoundedAlgHom.comp_assoc, f.compPullback_comp_restriction]
    _ = f.chainPullback g i j q hf hg := by
      dsimp only [chainPullback]
      rw [← BoundedAlgHom.comp_assoc, f.restriction_comp_pullback i i' j hi hf hf']
    _ = (f.compPullback g hb hc i k h).comp (C.atlas.restriction k q hkq) :=
      (f.compPullback_comp_restriction g hb hc i k h j q hf hg hkq).symm
    _ = ((f.compPullback g hb hc i k h).comp (C.atlas.restriction k k' hk)).comp
        (C.atlas.restriction k' q hk'q) := by
      rw [BoundedAlgHom.comp_assoc, ← C.atlas.restriction_comp]

/-- Compose arbitrary strong maps by constructing every admissible local
pullback through directed original intermediate and final charts. -/
def compOfDirected (f : StrongHom A B) (g : StrongHom B C)
    (hb : B.atlas.HasDirectedCharts) (hc : C.atlas.HasDirectedCharts) :
    StrongHom A C where
  baseMap := g.baseMap.comp f.baseMap
  target_exists i := by
    obtain ⟨j, hf⟩ := f.target_exists i
    obtain ⟨k, hg⟩ := g.target_exists j
    exact ⟨k, f.comp_admissible g i j k hf hg⟩
  pullback := f.compPullback g hb hc
  chart_comm := f.compPullback_chart g hb hc
  restriction_comm := f.compPullback_naturality g hb hc

@[simp]
theorem compOfDirected_baseMap (f : StrongHom A B) (g : StrongHom B C)
    (hb : B.atlas.HasDirectedCharts) (hc : C.atlas.HasDirectedCharts) :
    (f.compOfDirected g hb hc).baseMap = g.baseMap.comp f.baseMap := rfl

/-- At every admissible chain the constructed composite is exactly the
contravariant composite of its actual bounded pullbacks. -/
theorem compOfDirected_pullback (f : StrongHom A B) (g : StrongHom B C)
    (hb : B.atlas.HasDirectedCharts) (hc : C.atlas.HasDirectedCharts)
    (i : A.atlas.Index) (j : B.atlas.Index) (k : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart k))
    (h : (f.compOfDirected g hb hc).baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k)) :
    (f.compOfDirected g hb hc).pullback i k h =
      (f.pullback i j hf).comp (g.pullback j k hg) := by
  change f.compPullback g hb hc i k h = f.chainPullback g i j k hf hg
  simpa only [C.atlas.restriction_id, BoundedAlgHom.comp_id] using
    f.compPullback_comp_restriction g hb hc i k h j k hf hg Subset.rfl

/-- One bounded pullback per source chart detects the full strong map when
original target charts are directed. -/
theorem ext_of_directed {f g : StrongHom A B} (hd : B.atlas.HasDirectedCharts)
    (hb : f.baseMap = g.baseMap)
    (hp : ∀ i, ∃ (j : B.atlas.Index)
      (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)),
      f.pullback i j h = g.pullback i j (by rw [← hb]; exact h)) :
    f = g := by
  rcases f with ⟨fb, ft, fp, fc, fr⟩
  rcases g with ⟨gb, gt, gp, gc, gr⟩
  dsimp only at hb hp ⊢
  subst gb
  refine StrongHom.ext (f := ⟨fb, ft, fp, fc, fr⟩)
    (g := ⟨fb, gt, gp, gc, gr⟩) rfl ?_
  apply heq_of_eq
  funext i k h
  obtain ⟨j, hj, heq⟩ := hp i
  obtain ⟨q, hjq, hkq⟩ := hd j k
  have hq := hj.trans hjq
  have hf₁ := fr i i k q Subset.rfl hkq h hq
  have hf₂ := fr i i j q Subset.rfl hjq hj hq
  have hg₁ := gr i i k q Subset.rfl hkq h hq
  have hg₂ := gr i i j q Subset.rfl hjq hj hq
  simp only [A.atlas.restriction_id, BoundedAlgHom.id_comp] at hf₁ hf₂ hg₁ hg₂
  apply B.atlas.restriction_hom_ext k q hkq (A.atlas.algebra i)
  exact hf₁.symm.trans (hf₂.trans ((congrArg
    (fun ψ => ψ.comp (B.atlas.restriction j q hjq)) heq).trans
      (hg₂.symm.trans hg₁)))

@[simp]
theorem id_compOfDirected (f : StrongHom A B)
    (ha : A.atlas.HasDirectedCharts) (hb : B.atlas.HasDirectedCharts) :
    (id A).compOfDirected f ha hb = f := by
  refine ext_of_directed hb rfl ?_
  intro i
  obtain ⟨j, hf⟩ := f.target_exists i
  refine ⟨j, hf, ?_⟩
  rw [compOfDirected_pullback (id A) f ha hb i i j
    (by simp only [id, ContinuousMap.coe_id, Set.image_id, Subset.rfl]) hf hf]
  change (A.atlas.restriction i i _).comp (f.pullback i j hf) = _
  rw [A.atlas.restriction_id, BoundedAlgHom.id_comp]

@[simp]
theorem compOfDirected_id (f : StrongHom A B) (hb : B.atlas.HasDirectedCharts) :
    f.compOfDirected (id B) hb hb = f := by
  refine ext_of_directed hb rfl ?_
  intro i
  obtain ⟨j, hf⟩ := f.target_exists i
  refine ⟨j, hf, ?_⟩
  rw [compOfDirected_pullback f (id B) hb hb i j j hf
    (by simp only [id, ContinuousMap.coe_id, Set.image_id, Subset.rfl]) hf]
  change (f.pullback i j hf).comp (B.atlas.restriction j j _) = _
  rw [B.atlas.restriction_id, BoundedAlgHom.comp_id]

/-- Associativity is equality of the complete all-admissible strong maps. -/
theorem compOfDirected_assoc (f : StrongHom A B) (g : StrongHom B C)
    (h : StrongHom C D)
    (hb : B.atlas.HasDirectedCharts) (hc : C.atlas.HasDirectedCharts)
    (hd : D.atlas.HasDirectedCharts) :
    (f.compOfDirected g hb hc).compOfDirected h hc hd =
      f.compOfDirected (g.compOfDirected h hc hd) hb hd := by
  refine ext_of_directed hd rfl ?_
  intro i
  obtain ⟨j, hf⟩ := f.target_exists i
  obtain ⟨k, hg⟩ := g.target_exists j
  obtain ⟨l, hh⟩ := h.target_exists k
  have hfg := f.comp_admissible g i j k hf hg
  have hgh := g.comp_admissible h j k l hg hh
  have hfg_h := (f.compOfDirected g hb hc).comp_admissible h i k l hfg hh
  refine ⟨l, hfg_h, ?_⟩
  rw [compOfDirected_pullback (f.compOfDirected g hb hc) h hc hd i k l hfg hh hfg_h,
    compOfDirected_pullback f (g.compOfDirected h hc hd) hb hd i j l hf hgh,
    compOfDirected_pullback f g hb hc i j k hf hg hfg,
    compOfDirected_pullback g h hc hd j k l hg hh hgh,
    BoundedAlgHom.comp_assoc]

/-- The directed construction agrees with the published greatest-chart
construction as a full strong map. -/
theorem compOfDirected_eq_compOfTopCharts (f : StrongHom A B) (g : StrongHom B C)
    (hb : B.atlas.HasDirectedCharts) (hc : C.atlas.HasDirectedCharts)
    (b : B.atlas.Index)
    (hbt : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart b))
    (c : C.atlas.Index)
    (hct : ∀ j, Set.range (C.atlas.chart j) ⊆ Set.range (C.atlas.chart c)) :
    f.compOfDirected g hb hc = f.compOfTopCharts g b hbt c hct := by
  refine ext_of_directed hc rfl ?_
  intro i
  have hf := f.image_chart_top b hbt i
  have hg := g.image_chart_top c hct b
  have h := f.comp_admissible g i b c hf hg
  exact ⟨c, h, (f.compOfDirected_pullback g hb hc i b c hf hg h).trans
    (f.compOfTopCharts_pullback g b hbt c hct i b c hf hg h).symm⟩

/-- Extending chosen maps and composing their full strong extensions retain
exactly the original chosen bounded composite. -/
theorem ofDirected_comp (f : A ⟶ B) (g : B ⟶ C)
    (hb : B.atlas.HasDirectedCharts) (hc : C.atlas.HasDirectedCharts) :
    ofDirected (f ≫ g) hc =
      (ofDirected f hb).compOfDirected (ofDirected g hc) hb hc := by
  refine ext_of_directed hc rfl ?_
  intro i
  have hf := f.image_chart_subset i
  have hg := g.image_chart_subset (f.indexMap i)
  have h := (ofDirected f hb).comp_admissible (ofDirected g hc)
    i (f.indexMap i) (g.indexMap (f.indexMap i)) hf hg
  refine ⟨g.indexMap (f.indexMap i), h, ?_⟩
  have hs : (ofDirected (f ≫ g) hc).pullback i (g.indexMap (f.indexMap i)) h =
      (f.pullback i).comp (g.pullback (f.indexMap i)) :=
    ofDirected_pullback_selected (f ≫ g) hc i
  apply hs.trans
  rw [compOfDirected_pullback (ofDirected f hb) (ofDirected g hc) hb hc
    i (f.indexMap i) (g.indexMap (f.indexMap i)) hf hg h,
    ofDirected_pullback_selected f hb i,
    ofDirected_pullback_selected g hc (f.indexMap i)]

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

namespace Langlands.Analytic

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A supplied actual affinoid atlas presentation whose original chart
domains are pairwise directed under containment. -/
structure DirectedAtlasPresentation (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] where
  presentation : AffinoidAtlasPresentation.{u, v, w} K
  directed : presentation.atlas.HasDirectedCharts

namespace DirectedAtlasPresentation

instance : Category (DirectedAtlasPresentation.{u, v, w} K) where
  Hom A B := AffinoidAtlasPresentation.StrongHom A.presentation B.presentation
  id A := AffinoidAtlasPresentation.StrongHom.id A.presentation
  comp {_A B C} f g := f.compOfDirected g B.directed C.directed
  id_comp {A B} f := f.id_compOfDirected A.directed B.directed
  comp_id {_A B} f := f.compOfDirected_id B.directed
  assoc {_A B C D} f g h := f.compOfDirected_assoc g h B.directed C.directed D.directed

@[simp]
theorem baseMap_id (A : DirectedAtlasPresentation.{u, v, w} K) :
    (𝟙 A : A ⟶ A).baseMap = ContinuousMap.id A.presentation.space := rfl

@[simp]
theorem baseMap_comp {A B C : DirectedAtlasPresentation.{u, v, w} K}
    (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).baseMap = g.baseMap.comp f.baseMap := rfl

/-- Retain the actual spaces and continuous maps of directed presentations. -/
def spaceFunctor : DirectedAtlasPresentation.{u, v, w} K ⥤ TopCat.{v} where
  obj A := A.presentation.space
  map f := TopCat.ofHom f.baseMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Every greatest-chart presentation is a directed presentation on exactly
the same original atlas. -/
def ofTopChart (A : TopChartPresentation.{u, v, w} K) :
    DirectedAtlasPresentation.{u, v, w} K where
  presentation := A.presentation
  directed := A.presentation.atlas.hasDirectedCharts_of_top A.topChart A.top_contains

/-- The greatest-chart category embeds with its entire strong-map families. -/
def topChartFunctor :
    TopChartPresentation.{u, v, w} K ⥤ DirectedAtlasPresentation.{u, v, w} K where
  obj := ofTopChart
  map f := f
  map_id _ := rfl
  map_comp {_A B C} f g :=
    (f.compOfDirected_eq_compOfTopCharts g
      (ofTopChart B).directed (ofTopChart C).directed
      B.topChart B.top_contains C.topChart C.top_contains).symm

/-- The embedding keeps every strong map and has the identity inverse on Hom. -/
def topChartFullyFaithful :
    topChartFunctor (K := K) |>.FullyFaithful where
  preimage f := f
  map_preimage _ := rfl
  preimage_map _ := rfl

instance : (topChartFunctor (K := K)).Full := topChartFullyFaithful.full

instance : (topChartFunctor (K := K)).Faithful := topChartFullyFaithful.faithful

/-- The embedding retains the actual underlying-space diagram exactly. -/
theorem topChartFunctor_spaceFunctor :
    topChartFunctor (K := K) ⋙ spaceFunctor = TopChartPresentation.spaceFunctor := rfl

end DirectedAtlasPresentation

end Langlands.Analytic
