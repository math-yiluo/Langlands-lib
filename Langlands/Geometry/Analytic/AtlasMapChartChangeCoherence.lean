import Langlands.Geometry.Analytic.AtlasMapChartChangeNaturality

/-! # Coherence and reversal of arbitrary target-chart changes -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- A bounded factorization through an original subchart retains its ambient
chart equation after every bounded coefficient test. -/
theorem chart_eq_of_factor (i m : a.Index)
    (hmi : Set.range (a.chart m) ⊆ Set.range (a.chart i))
    (R T : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra i) R) (η : BoundedAlgHom K R T)
    (α : BoundedAlgHom K (a.algebra m) T)
    (hα : α.comp (a.restriction m i hmi) = η.comp φ)
    (x : BanachSpectrum T) :
    a.chart m (BanachSpectrum.comap α.toBoundedRingHom x) =
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom
        (BanachSpectrum.comap η.toBoundedRingHom x)) := by
  calc
    a.chart m (BanachSpectrum.comap α.toBoundedRingHom x) =
        a.chart i (BanachSpectrum.comap
          (α.comp (a.restriction m i hmi)).toBoundedRingHom x) :=
      (a.restriction_chart m i hmi _).symm
    _ = a.chart i (BanachSpectrum.comap (η.comp φ).toBoundedRingHom x) :=
      congrArg (fun q : BoundedAlgHom K (a.algebra i) T =>
        a.chart i (BanachSpectrum.comap q.toBoundedRingHom x)) hα
    _ = _ := rfl

/-- The universal chart-change law composes through an arbitrary intermediate
chart. Its proof uses actual finite test covers by triple common subcharts. -/
theorem IsMapChartChange.trans {i j k : a.Index} {R : PresentedAffinoidAlgebra K}
    {φ : BoundedAlgHom K (a.algebra i) R}
    {ψ : BoundedAlgHom K (a.algebra j) R}
    {χ : BoundedAlgHom K (a.algebra k) R}
    (hφ : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j))
    (hψ : a.IsMapChartChange i j R φ ψ)
    (hχ : a.IsMapChartChange j k R ψ χ) :
    a.IsMapChartChange i k R φ χ := by
  intro T η m hmi hmk α hα
  have hmj : ∀ x : BanachSpectrum T,
      a.chart m (BanachSpectrum.comap α.toBoundedRingHom x) ∈
        Set.range (a.chart j) := by
    intro x
    rw [a.chart_eq_of_factor i m hmi R T φ η α hα x]
    exact hφ _
  let c := a.mapImageChartCover m j T α hmj
  let d := c.mapPullbackCover T α (fun x => ⟨x, rfl⟩)
  have hlocal (t : Fin c.size) :
      (d.map t).restriction.comp (η.comp χ) =
        (d.map t).restriction.comp (α.comp (a.restriction m k hmk)) := by
    let D := a.restrictionDomain (c.index t) m (c.left_subset t)
    let Q := Domain.pullback α D
    let β : BoundedAlgHom K (a.algebra (c.index t)) Q.algebra :=
      Domain.pullbackMap α D
    have hβm : β.comp (a.restriction (c.index t) m (c.left_subset t)) =
        Q.baseMap.comp α := Domain.pullbackMap_comp_baseMap α D
    have hβ : β.comp
        (a.restriction (c.index t) i ((c.left_subset t).trans hmi)) =
        (Q.baseMap.comp η).comp φ := by
      calc
        β.comp (a.restriction (c.index t) i ((c.left_subset t).trans hmi)) =
            β.comp ((a.restriction (c.index t) m (c.left_subset t)).comp
              (a.restriction m i hmi)) :=
          congrArg (fun q : BoundedAlgHom K (a.algebra i) (a.algebra (c.index t)) =>
            β.comp q) (a.restriction_comp (c.index t) m i
              (c.left_subset t) hmi ((c.left_subset t).trans hmi))
        _ = (β.comp (a.restriction (c.index t) m (c.left_subset t))).comp
            (a.restriction m i hmi) := rfl
        _ = (Q.baseMap.comp α).comp (a.restriction m i hmi) :=
          congrArg (fun q : BoundedAlgHom K (a.algebra m) Q.algebra =>
            q.comp (a.restriction m i hmi)) hβm
        _ = Q.baseMap.comp (α.comp (a.restriction m i hmi)) := rfl
        _ = Q.baseMap.comp (η.comp φ) :=
          congrArg (fun q : BoundedAlgHom K (a.algebra i) T =>
            Q.baseMap.comp q) hα
        _ = (Q.baseMap.comp η).comp φ := rfl
    have hψt := hψ Q.algebra (Q.baseMap.comp η) (c.index t)
      ((c.left_subset t).trans hmi) (c.right_subset t) β hβ
    have hχt := hχ Q.algebra (Q.baseMap.comp η) (c.index t)
      (c.right_subset t) ((c.left_subset t).trans hmk) β hψt.symm
    change Q.baseMap.comp (η.comp χ) =
      Q.baseMap.comp (α.comp (a.restriction m k hmk))
    calc
      Q.baseMap.comp (η.comp χ) =
          β.comp (a.restriction (c.index t) k ((c.left_subset t).trans hmk)) := hχt
      _ = β.comp ((a.restriction (c.index t) m (c.left_subset t)).comp
            (a.restriction m k hmk)) :=
        congrArg (fun q : BoundedAlgHom K (a.algebra k) (a.algebra (c.index t)) =>
          β.comp q) (a.restriction_comp (c.index t) m k
            (c.left_subset t) hmk ((c.left_subset t).trans hmk))
      _ = (β.comp (a.restriction (c.index t) m (c.left_subset t))).comp
          (a.restriction m k hmk) := rfl
      _ = (Q.baseMap.comp α).comp (a.restriction m k hmk) :=
        congrArg (fun q : BoundedAlgHom K (a.algebra m) Q.algebra =>
          q.comp (a.restriction m k hmk)) hβm
      _ = Q.baseMap.comp (α.comp (a.restriction m k hmk)) := rfl
  apply BoundedAlgHom.ext
  intro b
  apply d.algebra_ext_of_restrict_eq
  intro t
  exact congrArg (fun q : BoundedAlgHom K (a.algebra k) (d.obj t).algebra => q b)
    (hlocal t)

/-- Changing target chart twice equals the direct change as a bounded map. -/
theorem changeMapChart_trans (i j k : a.Index) (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra i) R)
    (hj : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j))
    (hk : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart k))
    (hjk : ∀ x : BanachSpectrum R,
      a.chart j (BanachSpectrum.comap (a.changeMapChart i j R φ hj).toBoundedRingHom x)
        ∈ Set.range (a.chart k)) :
    a.changeMapChart j k R (a.changeMapChart i j R φ hj) hjk =
      a.changeMapChart i k R φ hk :=
  a.eq_changeMapChart i k R φ hk _
    ((a.changeMapChart_isMapChartChange i j R φ hj).trans a hj
      (a.changeMapChart_isMapChartChange j k R _ hjk))

/-- The original chart contains the entire image of the changed bounded map. -/
theorem changeMapChart_image_original (i j : a.Index) (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra i) R)
    (h : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j))
    (x : BanachSpectrum R) :
    a.chart j (BanachSpectrum.comap (a.changeMapChart i j R φ h).toBoundedRingHom x)
      ∈ Set.range (a.chart i) := by
  rw [a.changeMapChart_chart]
  exact ⟨_, rfl⟩

/-- Construct the reverse target-chart change on the same coefficient algebra. -/
def reverseMapChartChange (i j : a.Index) (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra i) R)
    (h : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j)) :
    BoundedAlgHom K (a.algebra i) R :=
  a.changeMapChart j i R (a.changeMapChart i j R φ h)
    (a.changeMapChart_image_original i j R φ h)

/-- Reversal recovers the original complete bounded coefficient map. -/
theorem reverseMapChartChange_eq (i j : a.Index) (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra i) R)
    (h : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j)) :
    a.reverseMapChartChange i j R φ h = φ :=
  (a.changeMapChart_trans i j i R φ h (fun _ => ⟨_, rfl⟩)
    (a.changeMapChart_image_original i j R φ h)).trans
      (a.changeMapChart_self i R φ _)

end Langlands.Analytic.IndexedAffinoidAtlas
