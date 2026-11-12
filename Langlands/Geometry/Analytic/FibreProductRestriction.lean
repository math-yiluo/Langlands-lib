import Langlands.Geometry.Analytic.FibreProductChartSystem
import Langlands.Geometry.Analytic.AtlasMapChartChangeCoherence
import Langlands.Geometry.Analytic.CoherentStrongChartChange
import Langlands.Geometry.Analytic.AtlasMapChartChangeRepresentation

/-! # Restrictions between fibre product charts with included ranges -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

theorem changeMapChart_congr {i j : a.Index} {R : PresentedAffinoidAlgebra K}
    {φ φ' : BoundedAlgHom K (a.algebra i) R} (e : φ = φ')
    (h : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j))
    (h' : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ'.toBoundedRingHom x) ∈ Set.range (a.chart j)) :
    a.changeMapChart i j R φ h = a.changeMapChart i j R φ' h' := by
  subst e
  rfl

/-- A map restricted from a common subchart is its own chart change. -/
theorem isMapChartChange_restriction (m i j : a.Index)
    (hmi : Set.range (a.chart m) ⊆ Set.range (a.chart i))
    (hmj : Set.range (a.chart m) ⊆ Set.range (a.chart j))
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (a.algebra m) R) :
    a.IsMapChartChange i j R (φ.comp (a.restriction m i hmi)) (φ.comp (a.restriction m j hmj)) := by
  intro T η l hli hlj α hα
  rw [← BoundedAlgHom.comp_assoc]
  exact a.originalChartRestriction_test_overlap i j m l hmi hmj hli hlj T (η.comp φ) α
    (by rw [BoundedAlgHom.comp_assoc]; exact hα.symm)

theorem changeMapChart_restriction (m i j : a.Index)
    (hmi : Set.range (a.chart m) ⊆ Set.range (a.chart i))
    (hmj : Set.range (a.chart m) ⊆ Set.range (a.chart j))
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (a.algebra m) R)
    (h : ∀ x : BanachSpectrum R, a.chart i (BanachSpectrum.comap
      (φ.comp (a.restriction m i hmi)).toBoundedRingHom x) ∈ Set.range (a.chart j)) :
    a.changeMapChart i j R (φ.comp (a.restriction m i hmi)) h =
      φ.comp (a.restriction m j hmj) :=
  (a.eq_changeMapChart i j R _ h _ (a.isMapChartChange_restriction m i j hmi hmj R φ)).symm

end IndexedAffinoidAtlas

namespace FibreProduct

open AffinoidAtlasPresentation

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)

variable {f g}

theorem leftPoint_mem_of_range_subset {p q : PairIndex f g}
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q))
    (x : BanachSpectrum (algebra f g p)) :
    A.atlas.chart p.1.1 (leftPoint f g p x) ∈ range (A.atlas.chart q.1.1) :=
  ((mem_range_chart_iff f g q _).1 (h ⟨x, rfl⟩)).1

theorem rightPoint_mem_of_range_subset {p q : PairIndex f g}
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q))
    (x : BanachSpectrum (algebra f g p)) :
    B.atlas.chart p.1.2 (rightPoint f g p x) ∈ range (B.atlas.chart q.1.2) :=
  ((mem_range_chart_iff f g q _).1 (h ⟨x, rfl⟩)).2

/-- Two families of legs over two pairs, related by chart changes, satisfy the pushout
condition over the second base chart if they do over the first. -/
theorem condition_of_changeMapChart {p q : PairIndex f g} {R : PresentedAffinoidAlgebra K}
    (α : BoundedAlgHom K (A.atlas.algebra p.1.1) R) (β : BoundedAlgHom K (B.atlas.algebra p.1.2) R)
    (α' : BoundedAlgHom K (A.atlas.algebra q.1.1) R) (β' : BoundedAlgHom K (B.atlas.algebra q.1.2) R)
    (hα : ∀ x : BanachSpectrum R, A.atlas.chart p.1.1 (BanachSpectrum.comap α.toBoundedRingHom x) ∈
      range (A.atlas.chart q.1.1))
    (hβ : ∀ x : BanachSpectrum R, B.atlas.chart p.1.2 (BanachSpectrum.comap β.toBoundedRingHom x) ∈
      range (B.atlas.chart q.1.2))
    (hα' : A.atlas.IsMapChartChange p.1.1 q.1.1 R α α')
    (hβ' : B.atlas.IsMapChartChange p.1.2 q.1.2 R β β')
    (hc : α.comp (leftBase f g p) = β.comp (rightBase f g p)) :
    α'.comp (leftBase f g q) = β'.comp (rightBase f g q) := by
  have hL : C.atlas.IsMapChartChange (base f g p) (base f g q) R
      (α.comp (leftBase f g p)) (α'.comp (leftBase f g q)) :=
    f.toStrongHom.mapAffinoidChart_isMapChartChange_of_coherent f.coherent p.1.1 q.1.1
      (base f g p) (base f g q) (isCommonBase_base f g p).1 (isCommonBase_base f g q).1
      R α α' hα hα'
  have hR : C.atlas.IsMapChartChange (base f g p) (base f g q) R
      (β.comp (rightBase f g p)) (β'.comp (rightBase f g q)) :=
    g.toStrongHom.mapAffinoidChart_isMapChartChange_of_coherent g.coherent p.1.2 q.1.2
      (base f g p) (base f g q) (isCommonBase_base f g p).2 (isCommonBase_base f g q).2
      R β β' hβ hβ'
  rw [hc] at hL
  have himg : ∀ x : BanachSpectrum R, C.atlas.chart (base f g p)
      (BanachSpectrum.comap (β.comp (rightBase f g p)).toBoundedRingHom x) ∈
        range (C.atlas.chart (base f g q)) := by
    intro x
    change C.atlas.chart (base f g p) (BanachSpectrum.comap (rightBase f g p).toBoundedRingHom
      (BanachSpectrum.comap β.toBoundedRingHom x)) ∈ _
    rw [g.chart_comm]
    exact (isCommonBase_base f g q).2 ⟨_, hβ x, rfl⟩
  exact (C.atlas.eq_changeMapChart _ _ R _ himg _ hL).trans
    (C.atlas.eq_changeMapChart _ _ R _ himg _ hR).symm

variable (f g)

/-- The first leg of the restriction: the leg of `p`, moved to the first chart of `q`. -/
def rangeLeft {p q : PairIndex f g}
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q)) :
    BoundedAlgHom K (A.atlas.algebra q.1.1) (algebra f g p) :=
  A.atlas.changeMapChart p.1.1 q.1.1 (algebra f g p) (leftMap f g p)
    (leftPoint_mem_of_range_subset h)

/-- The second leg of the restriction. -/
def rangeRight {p q : PairIndex f g}
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q)) :
    BoundedAlgHom K (B.atlas.algebra q.1.2) (algebra f g p) :=
  B.atlas.changeMapChart p.1.2 q.1.2 (algebra f g p) (rightMap f g p)
    (rightPoint_mem_of_range_subset h)

theorem rangeCompat {p q : PairIndex f g}
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q)) :
    (rangeLeft f g h).comp (leftBase f g q) = (rangeRight f g h).comp (rightBase f g q) :=
  condition_of_changeMapChart _ _ _ _ (leftPoint_mem_of_range_subset h)
    (rightPoint_mem_of_range_subset h)
    (A.atlas.changeMapChart_isMapChartChange _ _ _ _ _)
    (B.atlas.changeMapChart_isMapChartChange _ _ _ _ _)
    (AffinoidPushout.condition (leftBase f g p) (rightBase f g p))

/-- The restriction `O(q) → O(p)` for pairs whose chart ranges are included. -/
def rangeRestriction {p q : PairIndex f g}
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q)) :
    BoundedAlgHom K (algebra f g q) (algebra f g p) :=
  AffinoidPushout.lift (leftBase f g q) (rightBase f g q) (algebra f g p)
    (rangeLeft f g h) (rangeRight f g h) (rangeCompat f g h)

theorem rangeRestriction_comp_leftMap {p q : PairIndex f g}
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q)) :
    (rangeRestriction f g h).comp (leftMap f g q) = rangeLeft f g h :=
  AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _

theorem rangeRestriction_comp_rightMap {p q : PairIndex f g}
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q)) :
    (rangeRestriction f g h).comp (rightMap f g q) = rangeRight f g h :=
  AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _

/-- On a common subchart, the range restriction is compatible with the chart system
restrictions. -/
theorem restriction_comp_rangeRestriction {m p q : PairIndex f g} (hmp : Sub f g m p)
    (hmq : Sub f g m q)
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q)) :
    (restriction f g m p hmp).comp (rangeRestriction f g h) = restriction f g m q hmq := by
  apply AffinoidPushout.hom_ext
  · rw [BoundedAlgHom.comp_assoc, rangeRestriction_comp_leftMap, restriction_comp_leftMap]
    unfold rangeLeft
    rw [← A.atlas.changeMapChart_comp p.1.1 q.1.1 (algebra f g p) (algebra f g m) (leftMap f g p)
      (leftPoint_mem_of_range_subset h) (restriction f g m p hmp)
      (fun x => leftPoint_mem_of_range_subset h
        (BanachSpectrum.comap (restriction f g m p hmp).toBoundedRingHom x))]
    refine (A.atlas.changeMapChart_congr (j := q.1.1) (restriction_comp_leftMap f g m p hmp) _
      (fun x => ?_)).trans ?_
    · rw [← restriction_comp_leftMap f g m p hmp]
      exact leftPoint_mem_of_range_subset h
        (BanachSpectrum.comap (restriction f g m p hmp).toBoundedRingHom x)
    · exact A.atlas.changeMapChart_restriction m.1.1 p.1.1 q.1.1 hmp.1 hmq.1 _ _ _
  · rw [BoundedAlgHom.comp_assoc, rangeRestriction_comp_rightMap, restriction_comp_rightMap]
    unfold rangeRight
    rw [← B.atlas.changeMapChart_comp p.1.2 q.1.2 (algebra f g p) (algebra f g m) (rightMap f g p)
      (rightPoint_mem_of_range_subset h) (restriction f g m p hmp)
      (fun x => rightPoint_mem_of_range_subset h
        (BanachSpectrum.comap (restriction f g m p hmp).toBoundedRingHom x))]
    refine (B.atlas.changeMapChart_congr (j := q.1.2) (restriction_comp_rightMap f g m p hmp) _
      (fun x => ?_)).trans ?_
    · rw [← restriction_comp_rightMap f g m p hmp]
      exact rightPoint_mem_of_range_subset h
        (BanachSpectrum.comap (restriction f g m p hmp).toBoundedRingHom x)
    · exact B.atlas.changeMapChart_restriction m.1.2 p.1.2 q.1.2 hmp.2 hmq.2 _ _ _

/-- The range restriction pulls back points of the chart of `p` to themselves. -/
theorem chart_rangeRestriction {p q : PairIndex f g}
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q))
    (x : BanachSpectrum (algebra f g p)) :
    (chartSystem f g).chart q (BanachSpectrum.comap (rangeRestriction f g h).toBoundedRingHom x) =
      (chartSystem f g).chart p x := by
  let Q := chartSystem f g
  obtain ⟨t, ht⟩ := h ⟨x, rfl⟩
  obtain ⟨m, hmp, hmq, v, hvx, hvt⟩ := Q.chart_eq_iff.1 ht.symm
  have hvx' : Q.pull hmp v = x := hvx
  have hvt' : Q.pull hmq v = t := hvt
  rw [← ht, ← hvt', ← hvx']
  change Q.chart q (BanachSpectrum.comap
    ((restriction f g m p hmp).comp (rangeRestriction f g h)).toBoundedRingHom v) = _
  rw [restriction_comp_rangeRestriction f g hmp hmq h]
  rfl

theorem rangeRestriction_self (p : PairIndex f g) :
    rangeRestriction f g (subset_rfl : range ((chartSystem f g).chart p) ⊆ _) =
      BoundedAlgHom.id K (algebra f g p) := by
  apply AffinoidPushout.hom_ext
  · rw [rangeRestriction_comp_leftMap, BoundedAlgHom.id_comp]
    exact A.atlas.changeMapChart_self _ _ _ _
  · rw [rangeRestriction_comp_rightMap, BoundedAlgHom.id_comp]
    exact B.atlas.changeMapChart_self _ _ _ _

theorem rangeRestriction_comp {p q r : PairIndex f g}
    (hpq : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q))
    (hqr : range ((chartSystem f g).chart q) ⊆ range ((chartSystem f g).chart r)) :
    rangeRestriction f g (hpq.trans hqr) =
      (rangeRestriction f g hpq).comp (rangeRestriction f g hqr) := by
  apply AffinoidPushout.hom_ext
  · rw [rangeRestriction_comp_leftMap, BoundedAlgHom.comp_assoc, rangeRestriction_comp_leftMap]
    have h1 := A.atlas.changeMapChart_isMapChartChange p.1.1 q.1.1 (algebra f g p) (leftMap f g p)
      (leftPoint_mem_of_range_subset hpq)
    have h2 := (A.atlas.changeMapChart_isMapChartChange q.1.1 r.1.1 (algebra f g q) (leftMap f g q)
      (leftPoint_mem_of_range_subset hqr)).comp A.atlas (rangeRestriction f g hpq)
    rw [rangeRestriction_comp_leftMap] at h2
    exact (A.atlas.eq_changeMapChart _ _ _ _ _ _
      (h1.trans A.atlas (leftPoint_mem_of_range_subset hpq) h2)).symm
  · rw [rangeRestriction_comp_rightMap, BoundedAlgHom.comp_assoc, rangeRestriction_comp_rightMap]
    have h1 := B.atlas.changeMapChart_isMapChartChange p.1.2 q.1.2 (algebra f g p) (rightMap f g p)
      (rightPoint_mem_of_range_subset hpq)
    have h2 := (B.atlas.changeMapChart_isMapChartChange q.1.2 r.1.2 (algebra f g q) (rightMap f g q)
      (rightPoint_mem_of_range_subset hqr)).comp B.atlas (rangeRestriction f g hpq)
    rw [rangeRestriction_comp_rightMap] at h2
    exact (B.atlas.eq_changeMapChart _ _ _ _ _ _
      (h1.trans B.atlas (rightPoint_mem_of_range_subset hpq) h2)).symm

/-- The range restriction followed by a chart change of the first leg of `q` is a chart
change of the first leg of `p`. -/
theorem isMapChartChange_rangeRestriction_left {p q : PairIndex f g}
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q))
    (j : A.atlas.Index)
    (hq : ∀ x : BanachSpectrum (algebra f g q),
      A.atlas.chart q.1.1 (leftPoint f g q x) ∈ range (A.atlas.chart j)) :
    A.atlas.IsMapChartChange p.1.1 j (algebra f g p) (leftMap f g p)
      ((rangeRestriction f g h).comp
        (A.atlas.changeMapChart q.1.1 j (algebra f g q) (leftMap f g q) hq)) := by
  have e1 := (A.atlas.changeMapChart_isMapChartChange q.1.1 j (algebra f g q) (leftMap f g q)
    hq).comp A.atlas (rangeRestriction f g h)
  rw [rangeRestriction_comp_leftMap] at e1
  exact (A.atlas.changeMapChart_isMapChartChange p.1.1 q.1.1 (algebra f g p) (leftMap f g p)
    (leftPoint_mem_of_range_subset h)).trans A.atlas (leftPoint_mem_of_range_subset h) e1

/-- The range restriction followed by a chart change of the second leg of `q` is a chart
change of the second leg of `p`. -/
theorem isMapChartChange_rangeRestriction_right {p q : PairIndex f g}
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q))
    (j : B.atlas.Index)
    (hq : ∀ x : BanachSpectrum (algebra f g q),
      B.atlas.chart q.1.2 (rightPoint f g q x) ∈ range (B.atlas.chart j)) :
    B.atlas.IsMapChartChange p.1.2 j (algebra f g p) (rightMap f g p)
      ((rangeRestriction f g h).comp
        (B.atlas.changeMapChart q.1.2 j (algebra f g q) (rightMap f g q) hq)) := by
  have e1 := (B.atlas.changeMapChart_isMapChartChange q.1.2 j (algebra f g q) (rightMap f g q)
    hq).comp B.atlas (rangeRestriction f g h)
  rw [rangeRestriction_comp_rightMap] at e1
  exact (B.atlas.changeMapChart_isMapChartChange p.1.2 q.1.2 (algebra f g p) (rightMap f g p)
    (rightPoint_mem_of_range_subset h)).trans B.atlas (rightPoint_mem_of_range_subset h) e1

/-- The universal property of the range restriction: maps from `O(q)` whose points land in
the chart of `p` factor uniquely through it. -/
theorem rangeRestriction_universal {p q : PairIndex f g}
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q))
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (algebra f g q) R)
    (hφ : ∀ x : BanachSpectrum R, (chartSystem f g).chart q
      (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ range ((chartSystem f g).chart p)) :
    ∃! ψ : BoundedAlgHom K (algebra f g p) R, ψ.comp (rangeRestriction f g h) = φ := by
  have hα : ∀ x : BanachSpectrum R, A.atlas.chart q.1.1
      (BanachSpectrum.comap (φ.comp (leftMap f g q)).toBoundedRingHom x) ∈
        range (A.atlas.chart p.1.1) := fun x => ((mem_range_chart_iff f g p _).1 (hφ x)).1
  have hβ : ∀ x : BanachSpectrum R, B.atlas.chart q.1.2
      (BanachSpectrum.comap (φ.comp (rightMap f g q)).toBoundedRingHom x) ∈
        range (B.atlas.chart p.1.2) := fun x => ((mem_range_chart_iff f g p _).1 (hφ x)).2
  let α := A.atlas.changeMapChart q.1.1 p.1.1 R (φ.comp (leftMap f g q)) hα
  let β := B.atlas.changeMapChart q.1.2 p.1.2 R (φ.comp (rightMap f g q)) hβ
  have hαc := A.atlas.changeMapChart_isMapChartChange q.1.1 p.1.1 R _ hα
  have hβc := B.atlas.changeMapChart_isMapChartChange q.1.2 p.1.2 R _ hβ
  have hc : α.comp (leftBase f g p) = β.comp (rightBase f g p) :=
    condition_of_changeMapChart _ _ α β hα hβ hαc hβc (by
      rw [BoundedAlgHom.comp_assoc, BoundedAlgHom.comp_assoc]
      exact congrArg φ.comp (AffinoidPushout.condition (leftBase f g q) (rightBase f g q)))
  refine ⟨AffinoidPushout.lift (leftBase f g p) (rightBase f g p) R α β hc, ?_, ?_⟩
  · apply AffinoidPushout.hom_ext
    · rw [BoundedAlgHom.comp_assoc, rangeRestriction_comp_leftMap]
      have h1 := (A.atlas.changeMapChart_isMapChartChange p.1.1 q.1.1 (algebra f g p)
        (leftMap f g p) (leftPoint_mem_of_range_subset h)).comp A.atlas
          (AffinoidPushout.lift (leftBase f g p) (rightBase f g p) R α β hc)
      rw [AffinoidPushout.lift_comp_leftMap] at h1
      have h2 := hαc.trans A.atlas hα h1
      exact (A.atlas.eq_changeMapChart _ _ _ _ (fun x => ⟨_, rfl⟩) _ h2).trans
        (A.atlas.changeMapChart_self _ _ _ _)
    · rw [BoundedAlgHom.comp_assoc, rangeRestriction_comp_rightMap]
      have h1 := (B.atlas.changeMapChart_isMapChartChange p.1.2 q.1.2 (algebra f g p)
        (rightMap f g p) (rightPoint_mem_of_range_subset h)).comp B.atlas
          (AffinoidPushout.lift (leftBase f g p) (rightBase f g p) R α β hc)
      rw [AffinoidPushout.lift_comp_rightMap] at h1
      have h2 := hβc.trans B.atlas hβ h1
      exact (B.atlas.eq_changeMapChart _ _ _ _ (fun x => ⟨_, rfl⟩) _ h2).trans
        (B.atlas.changeMapChart_self _ _ _ _)
  · intro ψ hψ
    apply AffinoidPushout.hom_ext
    · rw [AffinoidPushout.lift_comp_leftMap]
      have hl : ∀ x : BanachSpectrum R, A.atlas.chart p.1.1
          (BanachSpectrum.comap (ψ.comp (leftMap f g p)).toBoundedRingHom x) ∈
            range (A.atlas.chart q.1.1) :=
        fun x => leftPoint_mem_of_range_subset h (BanachSpectrum.comap ψ.toBoundedRingHom x)
      have h1 := (A.atlas.changeMapChart_isMapChartChange p.1.1 q.1.1 (algebra f g p)
        (leftMap f g p) (leftPoint_mem_of_range_subset h)).comp A.atlas ψ
      have e1 : ψ.comp (A.atlas.changeMapChart p.1.1 q.1.1 (algebra f g p) (leftMap f g p)
          (leftPoint_mem_of_range_subset h)) = φ.comp (leftMap f g q) := by
        change ψ.comp (rangeLeft f g h) = _
        rw [← rangeRestriction_comp_leftMap, ← BoundedAlgHom.comp_assoc, hψ]
      rw [e1] at h1
      have e2 := A.atlas.eq_changeMapChart _ _ _ _ hl _ h1
      have hrev := A.atlas.changeMapChart_reverse_isMapChartChange p.1.1 q.1.1 R _ hl
      rw [← e2] at hrev
      exact A.atlas.eq_changeMapChart _ _ _ _ hα _ hrev
    · rw [AffinoidPushout.lift_comp_rightMap]
      have hl : ∀ x : BanachSpectrum R, B.atlas.chart p.1.2
          (BanachSpectrum.comap (ψ.comp (rightMap f g p)).toBoundedRingHom x) ∈
            range (B.atlas.chart q.1.2) :=
        fun x => rightPoint_mem_of_range_subset h (BanachSpectrum.comap ψ.toBoundedRingHom x)
      have h1 := (B.atlas.changeMapChart_isMapChartChange p.1.2 q.1.2 (algebra f g p)
        (rightMap f g p) (rightPoint_mem_of_range_subset h)).comp B.atlas ψ
      have e1 : ψ.comp (B.atlas.changeMapChart p.1.2 q.1.2 (algebra f g p) (rightMap f g p)
          (rightPoint_mem_of_range_subset h)) = φ.comp (rightMap f g q) := by
        change ψ.comp (rangeRight f g h) = _
        rw [← rangeRestriction_comp_rightMap, ← BoundedAlgHom.comp_assoc, hψ]
      rw [e1] at h1
      have e2 := B.atlas.eq_changeMapChart _ _ _ _ hl _ h1
      have hrev := B.atlas.changeMapChart_reverse_isMapChartChange p.1.2 q.1.2 R _ hl
      rw [← e2] at hrev
      exact B.atlas.eq_changeMapChart _ _ _ _ hβ _ hrev

end FibreProduct

end Langlands.Analytic
