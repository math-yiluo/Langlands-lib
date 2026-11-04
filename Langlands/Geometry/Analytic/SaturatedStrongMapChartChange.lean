import Langlands.Geometry.Analytic.SaturatedStrongChartChange
import Langlands.Geometry.Analytic.AtlasMapChartChangeCoherence

/-! # Applying strong maps to arbitrary affinoid chart changes -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Apply an actual strong pullback to an arbitrary bounded affinoid test
mapping into one original source chart. -/
def mapAffinoidChart (f : StrongHom A B) (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (A.atlas.algebra i) R) :
    BoundedAlgHom K (B.atlas.algebra j) R :=
  φ.comp (f.pullback i j h)

theorem mapAffinoidChart_chart (f : StrongHom A B)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (A.atlas.algebra i) R)
    (x : BanachSpectrum R) :
    B.atlas.chart j (BanachSpectrum.comap
        (f.mapAffinoidChart i j h R φ).toBoundedRingHom x) =
      f.baseMap (A.atlas.chart i (BanachSpectrum.comap φ.toBoundedRingHom x)) :=
  f.chart_comm i j h (BanachSpectrum.comap φ.toBoundedRingHom x)

/-- On a saturated source, applying a strong morphism preserves the full
chart-change relation for arbitrary affinoid coefficients. -/
theorem mapAffinoidChart_isMapChartChange (f : StrongHom A B)
    (ha : A.atlas.HasAllLocalDomains) (i i' : A.atlas.Index)
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
    have htest := f.pullback_isMapChartChange ha n j j' hnj hnj'
      Q.algebra θ m hmj hmj' (Q.baseMap.comp α) hfactor
    exact hright.trans htest
  apply BoundedAlgHom.ext
  intro b
  apply d.algebra_ext_of_restrict_eq
  intro t
  exact congrArg (fun q : BoundedAlgHom K (B.atlas.algebra j')
    (d.obj t).algebra => q b) (hlocal t)

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
