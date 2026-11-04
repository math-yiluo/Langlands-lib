import Langlands.Geometry.Analytic.SaturatedStrongMapChartChange

/-! # Intrinsic bounded compatibility for strong atlas-map data -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- The original bounded pullbacks agree through every common target subchart
on every presented-affinoid coefficient test. This is a law on the supplied
maps; it contains no extension or saturation output. -/
def HasCoherentPullbacks (f : StrongHom A B) : Prop :=
  ∀ (i : A.atlas.Index) (j k : B.atlas.Index)
    (hj : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hk : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart k)),
    B.atlas.IsMapChartChange j k (A.atlas.algebra i)
      (f.pullback i j hj) (f.pullback i k hk)

/-- The constructed source-saturated recovery discharges the intrinsic law. -/
theorem hasCoherentPullbacks_of_saturated (f : StrongHom A B)
    (ha : A.atlas.HasAllLocalDomains) : f.HasCoherentPullbacks :=
  f.pullback_isMapChartChange ha

/-- Intrinsic coherence recovers each original bounded map from every other
admissible target by the actual finite-cover chart-change construction. -/
theorem pullback_eq_changeTargetPullback_of_coherent (f : StrongHom A B)
    (hf : f.HasCoherentPullbacks) (i : A.atlas.Index) (j k : B.atlas.Index)
    (hj : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hk : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart k)) :
    f.pullback i k hk = f.changeTargetPullback i j k hj hk :=
  B.atlas.eq_changeMapChart j k (A.atlas.algebra i) (f.pullback i j hj)
    (f.pullback_image_chart i j k hj hk) _ (hf i j k hj hk)

/-- Equivalently, the supplied family is fixed by each constructed target
chart change. The reverse implication uses the proved universal test law. -/
theorem hasCoherentPullbacks_iff (f : StrongHom A B) :
    f.HasCoherentPullbacks ↔
      ∀ (i : A.atlas.Index) (j k : B.atlas.Index)
        (hj : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
        (hk : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart k)),
        f.pullback i k hk = f.changeTargetPullback i j k hj hk := by
  constructor
  · exact f.pullback_eq_changeTargetPullback_of_coherent
  · intro h i j k hj hk
    rw [h i j k hj hk]
    exact B.atlas.changeMapChart_isMapChartChange j k (A.atlas.algebra i) _
      (f.pullback_image_chart i j k hj hk)

/-- Actual identity restrictions satisfy full coefficient-test coherence
on an arbitrary original atlas. -/
theorem hasCoherentPullbacks_id (A : AffinoidAtlasPresentation.{u, v, w} K) :
    (id A).HasCoherentPullbacks := by
  intro i j k hj hk T η m hmj hmk α hα
  have hij : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart j) := by
    simpa only [id, ContinuousMap.coe_id, Set.image_id] using hj
  have hik : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart k) := by
    simpa only [id, ContinuousMap.coe_id, Set.image_id] using hk
  exact A.atlas.originalChartRestriction_test_overlap j k i m hij hik hmj hmk T η α
    hα.symm

/-- For two coherent families on arbitrary atlases, one complete admissible
bounded map per source chart determines the whole original family. -/
theorem ext_of_coherent {f g : StrongHom A B}
    (hf : f.HasCoherentPullbacks) (hg : g.HasCoherentPullbacks)
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
  have h₁ := (⟨fb, ft, fp, fc, fr⟩ : StrongHom A B).pullback_eq_changeTargetPullback_of_coherent
    hf i j k hj h
  have h₂ := (⟨fb, gt, gp, gc, gr⟩ : StrongHom A B).pullback_eq_changeTargetPullback_of_coherent
    hg i j k hj h
  dsimp only [changeTargetPullback] at h₁ h₂
  exact h₁.trans (by simpa only [heq] using h₂.symm)

/-- Intrinsic coherence suffices to preserve arbitrary source chart changes,
without saturation or directedness of either atlas. -/
theorem mapAffinoidChart_isMapChartChange_of_coherent (f : StrongHom A B)
    (hf : f.HasCoherentPullbacks) (i i' : A.atlas.Index)
    (j j' : B.atlas.Index)
    (hj : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hj' : f.baseMap '' Set.range (A.atlas.chart i') ⊆ Set.range (B.atlas.chart j'))
    (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (A.atlas.algebra i) R)
    (ψ : BoundedAlgHom K (A.atlas.algebra i') R)
    (hφ : ∀ x : BanachSpectrum R,
      A.atlas.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈
        Set.range (A.atlas.chart i'))
    (hψ : A.atlas.IsMapChartChange i i' R φ ψ) :
    B.atlas.IsMapChartChange j j' R
      (f.mapAffinoidChart i j hj R φ) (f.mapAffinoidChart i' j' hj' R ψ) := by
  intro T η m hmj hmj' α hα
  let Φ := η.comp φ
  let c := A.atlas.mapImageChartCover i i' T Φ
    (fun x => hφ (BanachSpectrum.comap η.toBoundedRingHom x))
  let hΦ : ∀ x : BanachSpectrum T,
      A.atlas.chart i (BanachSpectrum.comap Φ.toBoundedRingHom x) ∈
        A.atlas.mapChartImage i T Φ := fun x => ⟨x, rfl⟩
  let d := c.mapPullbackCover T Φ hΦ
  have hlocal (t : Fin c.size) :
      (d.map t).restriction.comp
          (η.comp (f.mapAffinoidChart i' j' hj' R ψ)) =
        (d.map t).restriction.comp (α.comp (B.atlas.restriction m j' hmj')) := by
    let n := c.index t
    let D := A.atlas.restrictionDomain n i (c.left_subset t)
    let Q := Domain.pullback Φ D
    let θ : BoundedAlgHom K (A.atlas.algebra n) Q.algebra :=
      Domain.pullbackMap Φ D
    have hθi : θ.comp (A.atlas.restriction n i (c.left_subset t)) =
        Q.baseMap.comp Φ := Domain.pullbackMap_comp_baseMap Φ D
    have hθi' : (Q.baseMap.comp η).comp ψ =
        θ.comp (A.atlas.restriction n i' (c.right_subset t)) :=
      hψ Q.algebra (Q.baseMap.comp η) n (c.left_subset t) (c.right_subset t) θ hθi
    have hnj : f.baseMap '' Set.range (A.atlas.chart n) ⊆
        Set.range (B.atlas.chart j) := (Set.image_mono (c.left_subset t)).trans hj
    have hnj' : f.baseMap '' Set.range (A.atlas.chart n) ⊆
        Set.range (B.atlas.chart j') := (Set.image_mono (c.right_subset t)).trans hj'
    have hfnj :
        (A.atlas.restriction n i (c.left_subset t)).comp (f.pullback i j hj) =
          f.pullback n j hnj := by
      simpa only [B.atlas.restriction_id, BoundedAlgHom.comp_id] using
        f.restriction_comm n i j j (c.left_subset t) Subset.rfl hnj hj
    have hfnj' :
        (A.atlas.restriction n i' (c.right_subset t)).comp (f.pullback i' j' hj') =
          f.pullback n j' hnj' := by
      simpa only [B.atlas.restriction_id, BoundedAlgHom.comp_id] using
        f.restriction_comm n i' j' j' (c.right_subset t) Subset.rfl hnj' hj'
    have hleft : θ.comp (f.pullback n j hnj) =
        Q.baseMap.comp (η.comp (f.mapAffinoidChart i j hj R φ)) := by
      calc
        θ.comp (f.pullback n j hnj) =
            (θ.comp (A.atlas.restriction n i (c.left_subset t))).comp
              (f.pullback i j hj) :=
          congrArg (fun q : BoundedAlgHom K (B.atlas.algebra j) (A.atlas.algebra n) =>
            θ.comp q) hfnj.symm
        _ = Q.baseMap.comp (η.comp (f.mapAffinoidChart i j hj R φ)) :=
          congrArg (fun q : BoundedAlgHom K (A.atlas.algebra i) Q.algebra =>
            q.comp (f.pullback i j hj)) hθi
    have hright : Q.baseMap.comp (η.comp (f.mapAffinoidChart i' j' hj' R ψ)) =
        θ.comp (f.pullback n j' hnj') := by
      calc
        Q.baseMap.comp (η.comp (f.mapAffinoidChart i' j' hj' R ψ)) =
            (θ.comp (A.atlas.restriction n i' (c.right_subset t))).comp
              (f.pullback i' j' hj') :=
          congrArg (fun q : BoundedAlgHom K (A.atlas.algebra i') Q.algebra =>
            q.comp (f.pullback i' j' hj')) hθi'
        _ = θ.comp (f.pullback n j' hnj') :=
          congrArg (fun q : BoundedAlgHom K (B.atlas.algebra j') (A.atlas.algebra n) =>
            θ.comp q) hfnj'
    have hfactor : (Q.baseMap.comp α).comp (B.atlas.restriction m j hmj) =
        θ.comp (f.pullback n j hnj) :=
      (congrArg (fun q : BoundedAlgHom K (B.atlas.algebra j) T =>
        Q.baseMap.comp q) hα).trans hleft.symm
    have htest := hf n j j' hnj hnj'
      Q.algebra θ m hmj hmj' (Q.baseMap.comp α) hfactor
    exact hright.trans htest
  apply BoundedAlgHom.ext
  intro b
  apply d.algebra_ext_of_restrict_eq
  intro t
  exact congrArg (fun q : BoundedAlgHom K (B.atlas.algebra j')
    (d.obj t).algebra => q b) (hlocal t)

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
