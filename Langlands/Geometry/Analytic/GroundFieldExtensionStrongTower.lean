import Langlands.Geometry.Analytic.GroundFieldExtensionAtlasTower
import Langlands.Geometry.Analytic.GroundFieldExtensionFunctor

/-! # The compatible strong comparison for a tower of ground fields -/

noncomputable section

universe u u' u'' v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

open Set Topology
open AffinoidAtlasPresentation PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension (towerEquiv towerEquiv_naturality)

section ChartwiseComparison

variable {F : Type u''} [NormedField F] [IsUltrametricDist F] [CompleteSpace F]

/-- Work with abstract endpoints when assembling the strong map, keeping
repeated reductions of the actual quotient atlases out of its proof fields. -/
private structure ChartwiseComparison (A B : AffinoidAtlasPresentation.{u'', v, w} F) where
  pointMap : A.space ≃ₜ B.space
  index : A.atlas.Index ≃ B.atlas.Index
  chartEquiv : ∀ i, BoundedAlgEquiv F (B.atlas.algebra (index i)) (A.atlas.algebra i)
  chart_comm : ∀ i x, pointMap (A.atlas.chart i x) =
    B.atlas.chart (index i) ((chartEquiv i).spectrumHomeomorph x)
  restriction_comm : ∀ i j (ha : range (A.atlas.chart i) ⊆ range (A.atlas.chart j))
    (hb : range (B.atlas.chart (index i)) ⊆ range (B.atlas.chart (index j))),
      (chartEquiv i).toBoundedAlgHom.comp (B.atlas.restriction (index i) (index j) hb) =
        (A.atlas.restriction i j ha).comp (chartEquiv j).toBoundedAlgHom

namespace ChartwiseComparison

variable {A B : AffinoidAtlasPresentation.{u'', v, w} F} (c : ChartwiseComparison A B)

private theorem image_chart (i : A.atlas.Index) :
    c.pointMap '' range (A.atlas.chart i) = range (B.atlas.chart (c.index i)) := by
  ext z
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨(c.chartEquiv i).spectrumHomeomorph s, (c.chart_comm i s).symm⟩
  · rintro ⟨t, rfl⟩
    let s := (c.chartEquiv i).spectrumHomeomorph.symm t
    exact ⟨A.atlas.chart i s, ⟨s, rfl⟩, (c.chart_comm i s).trans
      (congrArg (B.atlas.chart (c.index i)) ((c.chartEquiv i).spectrumHomeomorph.apply_symm_apply t))⟩

private theorem admissible (i : A.atlas.Index) (j : B.atlas.Index)
    (h : c.pointMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j)) :
    range (B.atlas.chart (c.index i)) ⊆ range (B.atlas.chart j) :=
  (c.image_chart i).superset.trans h

private def strong : StrongHom A B where
  baseMap := ⟨c.pointMap, c.pointMap.continuous⟩
  target_exists i := ⟨c.index i, (c.image_chart i).subset⟩
  pullback i j h := (c.chartEquiv i).toBoundedAlgHom.comp
    (B.atlas.restriction (c.index i) j (c.admissible i j h))
  chart_comm i j h x :=
    (B.atlas.restriction_chart (c.index i) j (c.admissible i j h)
      ((c.chartEquiv i).spectrumHomeomorph x)).trans (c.chart_comm i x).symm
  restriction_comm i i' j j' hi hj h h' := by
    let d := A.atlas.restriction i i' hi
    let e := fun t => (c.chartEquiv t).toBoundedAlgHom
    have hs : range (B.atlas.chart (c.index i)) ⊆ range (B.atlas.chart (c.index i')) :=
      (c.image_chart i).superset.trans ((image_mono hi).trans (c.image_chart i').subset)
    let hs₁ := c.admissible i j h
    let hs₂ := c.admissible i' j' h'
    let r := B.atlas.restriction (c.index i) (c.index i') hs
    let p := B.atlas.restriction (c.index i) j hs₁
    let q := B.atlas.restriction (c.index i') j' hs₂
    let t := B.atlas.restriction j j' hj
    have hchain : r.comp q = p.comp t :=
      (B.atlas.restriction_comp _ _ _ hs hs₂ (hs.trans hs₂)).symm.trans
        (B.atlas.restriction_comp _ _ _ hs₁ hj (hs.trans hs₂))
    change d.comp ((e i').comp q) = ((e i).comp p).comp t
    exact (BoundedAlgHom.comp_assoc d (e i') q).symm.trans
      ((congrArg (fun p => p.comp q) (c.restriction_comm i i' hi hs).symm).trans
        ((BoundedAlgHom.comp_assoc (e i) r q).trans
          ((congrArg (e i).comp hchain).trans (BoundedAlgHom.comp_assoc (e i) p t).symm)))

private def hom : CompatibleStrongHom A B where
  toStrongHom := c.strong
  compatible := c.strong.hasLocallyCompatiblePullbacks_iff.2 (by
    intro i j k hj hk
    have hj₀ := c.admissible i j hj
    have hk₀ := c.admissible i k hk
    have hj₁ : (StrongHom.id B).baseMap '' range (B.atlas.chart (c.index i)) ⊆
        range (B.atlas.chart j) := by
      simpa only [StrongHom.id, ContinuousMap.coe_id, image_id] using hj₀
    have hk₁ : (StrongHom.id B).baseMap '' range (B.atlas.chart (c.index i)) ⊆
        range (B.atlas.chart k) := by
      simpa only [StrongHom.id, ContinuousMap.coe_id, image_id] using hk₀
    exact (StrongHom.hasCoherentPullbacks_id B (c.index i) j k hj₁ hk₁).comp B.atlas
      (c.chartEquiv i).toBoundedAlgHom)

private theorem isQuasiIso : c.hom.toStrongHom.IsQuasiIso := by
  refine ⟨c.pointMap.isHomeomorph, ?_⟩
  intro i j h
  let hs := c.admissible i j h
  let e := c.chartEquiv i
  let r := B.atlas.restriction (c.index i) j hs
  change Represents F (e.toBoundedAlgHom.comp r)
    (B.atlas.chart j ⁻¹' (c.pointMap '' range (A.atlas.chart i)))
  rw [c.image_chart]
  exact (B.atlas.restriction_represents (c.index i) j hs).postcomp_equiv e

private theorem pullback_same (i : A.atlas.Index)
    (h : c.hom.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart (c.index i))) :
    c.hom.pullback i (c.index i) h = (c.chartEquiv i).toBoundedAlgHom := by
  change (c.chartEquiv i).toBoundedAlgHom.comp (B.atlas.restriction _ _ _) = _
  rw [B.atlas.restriction_id, BoundedAlgHom.comp_id]

/-- Two chartwise comparisons with inverse point maps, whose matching chart
equivalences cancel after the source restriction, compose to the identity
compatible map, including all bounded pullbacks. -/
private theorem hom_comp_hom (d : ChartwiseComparison B A)
    (hp : ∀ x, d.pointMap (c.pointMap x) = x)
    (hchart : ∀ i (h : range (A.atlas.chart (d.index (c.index i))) ⊆ range (A.atlas.chart i))
      (x : A.atlas.algebra i),
      c.chartEquiv i (d.chartEquiv (c.index i) (A.atlas.restriction _ i h x)) = x) :
    c.hom.comp d.hom = CompatibleStrongHom.id A := by
  have hb : (c.hom.comp d.hom).baseMap = (CompatibleStrongHom.id A).baseMap :=
    ContinuousMap.ext fun x => hp x
  refine CompatibleStrongHom.ext_of_pullback hb fun i => ?_
  have h₁ : c.hom.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart (c.index i)) :=
    (c.image_chart i).subset
  have hr : range (A.atlas.chart (d.index (c.index i))) ⊆ range (A.atlas.chart i) := by
    rw [← d.image_chart, ← c.image_chart, image_image]
    rintro _ ⟨x, hx, rfl⟩
    simpa only [hp] using hx
  have h₂ : d.hom.baseMap '' range (B.atlas.chart (c.index i)) ⊆ range (A.atlas.chart i) :=
    (d.image_chart (c.index i)).subset.trans hr
  have h := c.hom.toStrongHom.comp_admissible d.hom.toStrongHom i (c.index i) i h₁ h₂
  refine ⟨i, h, ?_⟩
  refine (CompatibleStrongHom.comp_pullback c.hom d.hom i (c.index i) i h₁ h₂ h).trans ?_
  rw [c.pullback_same i h₁]
  refine Eq.trans ?_ (A.atlas.restriction_id i Subset.rfl).symm
  apply BoundedAlgHom.ext
  intro x
  exact hchart i (d.admissible (c.index i) i h₂) x

end ChartwiseComparison
end ChartwiseComparison

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  (M : Type u'') [NormedField M] [IsUltrametricDist M] [CompleteSpace M]
  [NormedAlgebra L M] [NormedAlgebra K M] [IsScalarTower K L M]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

local notation "D" => presentation K M a
local notation "S" => presentation L M (atlas K L a)
local notation "H" => towerHomeomorph K L M a

/-- The bounded pullback for matching charts, before composing with restriction. -/
abbrev towerChartEquiv (i : a.Index) :
    BoundedAlgEquiv M ((S).atlas.algebra i) ((D).atlas.algebra i) :=
  towerEquiv K L M (a.algebra i)

/-- The chart equivalences intertwine the actual bounded restrictions. -/
theorem towerChartEquiv_restriction (i j : a.Index)
    (hd : range ((D).atlas.chart i) ⊆ range ((D).atlas.chart j))
    (hs : range ((S).atlas.chart i) ⊆ range ((S).atlas.chart j)) :
    (towerChartEquiv K L M a i).toBoundedAlgHom.comp ((S).atlas.restriction i j hs) =
      ((D).atlas.restriction i j hd).comp (towerChartEquiv K L M a j).toBoundedAlgHom :=
  towerEquiv_naturality K L M
    (a.restriction i j ((range_chart_subset_iff K M a i j).1 hd))

/-- A pair is admissible for the tower comparison exactly when the
corresponding source index is contained in the target index. -/
theorem towerAdmissible_iff (i j : a.Index) :
    H '' range ((D).atlas.chart i) ⊆ range ((S).atlas.chart j) ↔
      range ((S).atlas.chart i) ⊆ range ((S).atlas.chart j) :=
  congrArg (fun U : Set (S).space => U ⊆ range ((S).atlas.chart j))
    (towerHomeomorph_image_chart K L M a i) |>.to_iff

private def towerChartwiseComparison : ChartwiseComparison (A := D) (B := S) where
  pointMap := H
  index := Equiv.refl a.Index
  chartEquiv := towerChartEquiv K L M a
  chart_comm := towerHomeomorph_chart K L M a
  restriction_comm := towerChartEquiv_restriction K L M a

/-- The compatible strong comparison from direct to successive scalar
extension with full bounded pullbacks on all admissible chart pairs. -/
def towerCompatibleHom : CompatibleStrongHom D S :=
  (towerChartwiseComparison K L M a).hom

/-- The base map is the actual quotient tower homeomorphism. -/
theorem towerCompatibleHom_apply (x : (D).space) :
    (towerCompatibleHom K L M a).baseMap x = H x := rfl

/-- The chart restrictions give full domain representation at every pair,
not only on matching indices. -/
theorem towerCompatibleHom_isQuasiIso : (towerCompatibleHom K L M a).toStrongHom.IsQuasiIso :=
  (towerChartwiseComparison K L M a).isQuasiIso

/-- The bounded pullback is restriction followed by the matching chart comparison. -/
theorem towerCompatibleHom_pullback (i j : a.Index)
    (h : (towerCompatibleHom K L M a).baseMap '' range ((D).atlas.chart i) ⊆
      range ((S).atlas.chart j)) :
    (towerCompatibleHom K L M a).pullback i j h =
      (towerChartEquiv K L M a i).toBoundedAlgHom.comp
        ((S).atlas.restriction i j ((towerAdmissible_iff K L M a i j).1 h)) := rfl

/-- In particular, the matching-index pullback is the full bounded tower
comparison and not just its spectrum map. -/
theorem towerCompatibleHom_pullback_same (i : a.Index)
    (h : (towerCompatibleHom K L M a).baseMap '' range ((D).atlas.chart i) ⊆
      range ((S).atlas.chart i)) :
    (towerCompatibleHom K L M a).pullback i i h = (towerChartEquiv K L M a i).toBoundedAlgHom :=
  (towerChartwiseComparison K L M a).pullback_same i h

/-- The inverse chart equivalences intertwine the restrictions in the
other direction. -/
theorem towerChartEquiv_symm_restriction (i j : a.Index)
    (hd : range ((D).atlas.chart i) ⊆ range ((D).atlas.chart j))
    (hs : range ((S).atlas.chart i) ⊆ range ((S).atlas.chart j)) :
    (towerChartEquiv K L M a i).symm.toBoundedAlgHom.comp ((D).atlas.restriction i j hd) =
      ((S).atlas.restriction i j hs).comp (towerChartEquiv K L M a j).symm.toBoundedAlgHom := by
  apply BoundedAlgHom.ext
  intro x
  let ei := towerChartEquiv K L M a i
  let ej := towerChartEquiv K L M a j
  let rd := (D).atlas.restriction i j hd
  let rs := (S).atlas.restriction i j hs
  change ei.symm (rd x) = rs (ej.symm x)
  have h : ei (rs (ej.symm x)) = rd (ej (ej.symm x)) :=
    congrArg (fun φ : BoundedAlgHom M ((S).atlas.algebra j) ((D).atlas.algebra i) =>
      φ (ej.symm x)) (towerChartEquiv_restriction K L M a i j hd hs)
  have hx : rd (ej (ej.symm x)) = rd x := congrArg rd (ej.apply_symm_apply x)
  exact (congrArg ei.symm (h.trans hx).symm).trans (ei.symm_apply_apply _)

private def towerChartwiseInverse : ChartwiseComparison (A := S) (B := D) where
  pointMap := (towerHomeomorph K L M a).symm
  index := Equiv.refl a.Index
  chartEquiv i := (towerChartEquiv K L M a i).symm
  chart_comm i x := towerHomeomorph_symm_chart K L M a i x
  restriction_comm i j ha hb := towerChartEquiv_symm_restriction K L M a i j hb ha

/-- The inverse compatible strong comparison, from successive to direct
scalar extension. -/
def towerCompatibleInv : CompatibleStrongHom S D :=
  (towerChartwiseInverse K L M a).hom

/-- The base map of the inverse is the inverse tower homeomorphism. -/
theorem towerCompatibleInv_apply (x : (S).space) :
    (towerCompatibleInv K L M a).baseMap x = (towerHomeomorph K L M a).symm x := rfl

/-- The inverse comparison is also a strong quasi-isomorphism. -/
theorem towerCompatibleInv_isQuasiIso :
    (towerCompatibleInv K L M a).toStrongHom.IsQuasiIso :=
  (towerChartwiseInverse K L M a).isQuasiIso

/-- At matching indices the inverse pullback is the inverse bounded
tower equivalence. -/
theorem towerCompatibleInv_pullback_same (i : a.Index)
    (h : (towerCompatibleInv K L M a).baseMap '' range ((S).atlas.chart i) ⊆
      range ((D).atlas.chart i)) :
    (towerCompatibleInv K L M a).pullback i i h =
      (towerChartEquiv K L M a i).symm.toBoundedAlgHom :=
  (towerChartwiseInverse K L M a).pullback_same i h

private theorem towerInverse_points (x : (D).space) :
    (towerChartwiseInverse K L M a).pointMap ((towerChartwiseComparison K L M a).pointMap x) = x :=
  (towerHomeomorph K L M a).symm_apply_apply x

private theorem towerInverse_points' (x : (S).space) :
    (towerChartwiseComparison K L M a).pointMap ((towerChartwiseInverse K L M a).pointMap x) = x :=
  (towerHomeomorph K L M a).apply_symm_apply x

private theorem towerInverse_charts (i : (D).atlas.Index)
    (h : range ((D).atlas.chart ((towerChartwiseInverse K L M a).index
      ((towerChartwiseComparison K L M a).index i))) ⊆ range ((D).atlas.chart i))
    (x : (D).atlas.algebra i) :
    (towerChartwiseComparison K L M a).chartEquiv i
      ((towerChartwiseInverse K L M a).chartEquiv ((towerChartwiseComparison K L M a).index i)
        ((D).atlas.restriction _ i h x)) = x := by
  have hr := (D).atlas.restriction_id i h
  exact ((towerChartEquiv K L M a i).apply_symm_apply _).trans
    (congrArg (fun φ : BoundedAlgHom M ((D).atlas.algebra i) ((D).atlas.algebra i) => φ x) hr)

private theorem towerInverse_charts' (i : (S).atlas.Index)
    (h : range ((S).atlas.chart ((towerChartwiseComparison K L M a).index
      ((towerChartwiseInverse K L M a).index i))) ⊆ range ((S).atlas.chart i))
    (x : (S).atlas.algebra i) :
    (towerChartwiseInverse K L M a).chartEquiv i
      ((towerChartwiseComparison K L M a).chartEquiv ((towerChartwiseInverse K L M a).index i)
        ((S).atlas.restriction _ i h x)) = x := by
  have hr := (S).atlas.restriction_id i h
  exact ((towerChartEquiv K L M a i).symm_apply_apply _).trans
    (congrArg (fun φ : BoundedAlgHom M ((S).atlas.algebra i) ((S).atlas.algebra i) => φ x) hr)

/-- Comparing and then comparing back is the identity compatible map of the
direct extension, including all bounded pullbacks. -/
theorem towerCompatibleHom_comp_inv :
    (towerCompatibleHom K L M a).comp (towerCompatibleInv K L M a) =
      CompatibleStrongHom.id D :=
  (towerChartwiseComparison K L M a).hom_comp_hom (towerChartwiseInverse K L M a)
    (towerInverse_points K L M a) (towerInverse_charts K L M a)

/-- Comparing back and then comparing is the identity compatible map of the
successive extension, including all bounded pullbacks. -/
theorem towerCompatibleInv_comp_hom :
    (towerCompatibleInv K L M a).comp (towerCompatibleHom K L M a) =
      CompatibleStrongHom.id S :=
  (towerChartwiseInverse K L M a).hom_comp_hom (towerChartwiseComparison K L M a)
    (towerInverse_points' K L M a) (towerInverse_charts' K L M a)

end Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension
