import Langlands.Geometry.Analytic.AffineGroundFieldComparison.Points
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedMap

/-! # The strong affine ground field comparison, from the fixed-radius statement -/

noncomputable section

universe u u' v

namespace Langlands.Analytic.AffineAnalytification.GroundFieldComparison

open Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation
open PresentedAffinoidAlgebra.GroundFieldExtension (iota map_iota iota_coordinate map_coordinate
  comap_injective_of_represents represents_range)
open scoped TensorProduct

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
  (hfixed : AffineAnalytificationChartBaseChangeStatement.{u, u', v})

/-- The source atlas: the ground field extension of the affine atlas of `P`. -/
abbrev src := IndexedAffinoidAtlas.GroundFieldExtension.presentation K L (atlas K P)
/-- The target atlas: the affine atlas of the base-change presentation over `L`. -/
abbrev tgt := presentation L (Q K L P)

/-- The point map carries the extended source chart `i` into the target chart `j`. -/
abbrev admissible (i : ChartIndex K P) (j : ChartIndex L (Q K L P)) : Prop :=
  pointFun K L P hfixed '' range ((src K L P).atlas.chart i) ⊆ range ((tgt K L P).atlas.chart j)

theorem exists_admissible (i : ChartIndex K P) : ∃ j, admissible K L P hfixed i j := by
  refine ⟨representative L (Q K L P) (level K L P i), ?_⟩
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  change chartPoint K L P hfixed i s ∈ range (chart L (Q K L P) _)
  rw [range_representative]
  exact ⟨_, rfl⟩

/-- A raw `L`-chart index dominating both `level i` and the target index `j`. -/
abbrev large (i : ChartIndex K P) (j : ChartIndex L (Q K L P)) : ℕ :=
  max (level K L P i) j.val

theorem large_ge (i : ChartIndex K P) (j : ChartIndex L (Q K L P)) :
    AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L (large K L P i j) :=
  (le_radius_level K L P i).trans ((AnalyticAffineSpace.radius_le_radius_iff L).2 (le_max_left _ _))

/-- The raw restriction of `Q` from `large i j` to the target chart `j`. -/
abbrev largeRes (i : ChartIndex K P) (j : ChartIndex L (Q K L P)) :
    BoundedAlgHom L (algebra L (Q K L P) (large K L P i j)) (algebra L (Q K L P) j.val) :=
  restriction L (Q K L P) (le_max_right (level K L P i) j.val)

/-- The mixed-radius pullback from the raw chart `large i j` to the extended chart `i`. -/
abbrev largePull (i : ChartIndex K P) (j : ChartIndex L (Q K L P)) :
    BoundedAlgHom L (algebra L (Q K L P) (large K L P i j)) (E K L P i) :=
  rawPull K L P hfixed i _ (large_ge K L P i j)

theorem hasImageIn_largeRes (i : ChartIndex K P) (j : ChartIndex L (Q K L P))
    (h : admissible K L P hfixed i j) :
    HasImageIn L (largePull K L P hfixed i j)
      (range (BanachSpectrum.comap (largeRes K L P i j).toBoundedRingHom)) := by
  intro s
  have hy := h (show pointFun K L P hfixed ((src K L P).atlas.chart i s) ∈
    pointFun K L P hfixed '' range ((src K L P).atlas.chart i) from ⟨_, ⟨s, rfl⟩, rfl⟩)
  obtain ⟨t, ht⟩ := hy
  refine ⟨t, (isClosedEmbedding_chart L (Q K L P) (large K L P i j)).injective ?_⟩
  exact (chart_pull L (Q K L P) (le_max_right (level K L P i) j.val) t).trans
    (ht.trans (chartPoint_eq K L P hfixed i _ (large_ge K L P i j) s))

theorem existsUnique_fact (i : ChartIndex K P) (j : ChartIndex L (Q K L P))
    (h : admissible K L P hfixed i j) :
    ∃! f : BoundedAlgHom L (algebra L (Q K L P) j.val) (E K L P i),
      f.comp (largeRes K L P i j) = largePull K L P hfixed i j :=
  (represents_restriction L (Q K L P) (le_max_right (level K L P i) j.val)).2.2
    _ _ (hasImageIn_largeRes K L P hfixed i j h)

/-- Factor through every containing original target chart, even when its
numeric radius is smaller than the source radius. -/
def fact (i : ChartIndex K P) (j : ChartIndex L (Q K L P)) (h : admissible K L P hfixed i j) :
    BoundedAlgHom L ((tgt K L P).atlas.algebra j) ((src K L P).atlas.algebra i) :=
  Classical.choose (existsUnique_fact K L P hfixed i j h)

theorem fact_comp (i : ChartIndex K P) (j : ChartIndex L (Q K L P))
    (h : admissible K L P hfixed i j) :
    (fact K L P hfixed i j h).comp (largeRes K L P i j) = largePull K L P hfixed i j :=
  (Classical.choose_spec (existsUnique_fact K L P hfixed i j h)).1

theorem fact_chart_comm (i : ChartIndex K P) (j : ChartIndex L (Q K L P))
    (h : admissible K L P hfixed i j) (s : BanachSpectrum (E K L P i)) :
    (tgt K L P).atlas.chart j (BanachSpectrum.comap (fact K L P hfixed i j h).toBoundedRingHom s) =
      pointFun K L P hfixed ((src K L P).atlas.chart i s) := by
  let t := BanachSpectrum.comap (fact K L P hfixed i j h).toBoundedRingHom s
  have he := chart_pull L (Q K L P) (le_max_right (level K L P i) j.val) t
  change chart L (Q K L P) (large K L P i j) (BanachSpectrum.comap
    (largeRes K L P i j).toBoundedRingHom
      (BanachSpectrum.comap (fact K L P hfixed i j h).toBoundedRingHom s)) = _ at he
  have hc := (PresentedAffinoidAlgebra.GroundFieldExtension.comap_comp
    (fact K L P hfixed i j h) (largeRes K L P i j) s).symm.trans
      (congrArg (fun f : BoundedAlgHom L (algebra L (Q K L P) (large K L P i j)) (E K L P i) =>
        BanachSpectrum.comap f.toBoundedRingHom s) (fact_comp K L P hfixed i j h))
  exact he.symm.trans ((congrArg (chart L (Q K L P) (large K L P i j)) hc).trans
    (chartPoint_eq K L P hfixed i _ (large_ge K L P i j) s).symm)

theorem fact_algebraMap (i : ChartIndex K P) (j : ChartIndex L (Q K L P))
    (h : admissible K L P hfixed i j) (a : A) :
    fact K L P hfixed i j h
      (PolynomialLocus.algebraMap (Q K L P) (rL K L P j.val) ((1 : L) ⊗ₜ[K] a)) =
      iota K L (algebra K P i.val) (PolynomialLocus.algebraMap P (rK K P i) a) := by
  let b := PolynomialLocus.algebraMap (Q K L P) (rL K L P (large K L P i j)) ((1 : L) ⊗ₜ[K] a)
  have hle := AnalyticAffineSpace.polyradius_le L (Q K L P).arity (le_max_right (level K L P i) j.val)
  have hres := PolynomialLocus.restriction_algebraMap (Q K L P)
    (rL K L P (large K L P i j)) (rL K L P j.val) hle ((1 : L) ⊗ₜ[K] a)
  exact (congrArg (fun c : algebra L (Q K L P) j.val => fact K L P hfixed i j h c) hres).symm.trans
    ((congrArg (fun f : BoundedAlgHom L _ (E K L P i) => f b) (fact_comp K L P hfixed i j h)).trans
      (rawPull_algebraMap K L P hfixed i _ (large_ge K L P i j) a))

theorem fact_coordinate (i : ChartIndex K P) (j : ChartIndex L (Q K L P))
    (h : admissible K L P hfixed i j) (t : Fin P.arity) :
    fact K L P hfixed i j h (coordinate L (algebra L (Q K L P) j.val) t) =
      coordinate L (E K L P i) t := by
  let b := coordinate L (algebra L (Q K L P) (large K L P i j)) t
  let hle := AnalyticAffineSpace.polyradius_le L (Q K L P).arity (le_max_right (level K L P i) j.val)
  have hres := PolynomialLocus.restriction_coordinate (Q K L P)
    (rL K L P (large K L P i j)) (rL K L P j.val) hle t
  exact (congrArg (fun c : algebra L (Q K L P) j.val => fact K L P hfixed i j h c) hres).symm.trans
    ((congrArg (fun f : BoundedAlgHom L _ (E K L P i) => f b) (fact_comp K L P hfixed i j h)).trans
      (rawPull_coordinate K L P hfixed i _ (large_ge K L P i j) t))

theorem fact_represents (i : ChartIndex K P) (j : ChartIndex L (Q K L P))
    (h : admissible K L P hfixed i j) :
    Represents L (fact K L P hfixed i j h)
      (range (BanachSpectrum.comap (fact K L P hfixed i j h).toBoundedRingHom)) := by
  have hr := represents_restriction L (Q K L P) (le_max_right (level K L P i) j.val)
  have hp := rawPull_represents K L P hfixed i (large K L P i j) (large_ge K L P i j)
  change Represents L (largePull K L P hfixed i j) _ at hp
  rw [← fact_comp K L P hfixed i j h] at hp
  exact represents_range (hr.of_comp_of_injective hp (comap_injective_of_represents hr))

omit [IsUltrametricDist K] [CompleteSpace K] [CompleteSpace L] in
theorem rawRestriction_trans {m n q : ℕ} (hmn : m ≤ n) (hnq : n ≤ q) :
    (restriction L (Q K L P) hmn).comp (restriction L (Q K L P) hnq) =
      restriction L (Q K L P) (hmn.trans hnq) :=
  (PolynomialLocus.restriction_trans (Q K L P) (rL K L P q) (rL K L P n)
    (AnalyticAffineSpace.polyradius_le L (Q K L P).arity hnq) (rL K L P m)
    (AnalyticAffineSpace.polyradius_le L (Q K L P).arity hmn)).symm

theorem fact_comp_at (i : ChartIndex K P) (j : ChartIndex L (Q K L P))
    (h : admissible K L P hfixed i j) {n : ℕ} (hn : large K L P i j ≤ n)
    (hr : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L n) :
    (fact K L P hfixed i j h).comp
      (restriction L (Q K L P) ((le_max_right (level K L P i) j.val).trans hn)) =
      rawPull K L P hfixed i n hr := by
  let f := fact K L P hfixed i j h
  let r := largeRes K L P i j
  let s := restriction L (Q K L P) hn
  have hres := rawRestriction_trans K L P (le_max_right (level K L P i) j.val) hn
  have hf : f.comp r = largePull K L P hfixed i j := fact_comp K L P hfixed i j h
  exact (congrArg (f.comp) hres.symm).trans
    ((BoundedAlgHom.comp_assoc f r s).symm.trans
      ((congrArg (fun g : BoundedAlgHom L _ (E K L P i) => g.comp s) hf).trans
        (rawPull_comp K L P hfixed i hn (large_ge K L P i j) hr)))

open IndexedAffinoidAtlas.GroundFieldExtension (range_chart_subset_iff) in
theorem fact_restriction_comm (i i' : ChartIndex K P) (j j' : ChartIndex L (Q K L P))
    (hi : range ((src K L P).atlas.chart i) ⊆ range ((src K L P).atlas.chart i'))
    (hj : range ((tgt K L P).atlas.chart j) ⊆ range ((tgt K L P).atlas.chart j'))
    (h : admissible K L P hfixed i j) (h' : admissible K L P hfixed i' j') :
    ((src K L P).atlas.restriction i i' hi).comp (fact K L P hfixed i' j' h') =
      (fact K L P hfixed i j h).comp ((tgt K L P).atlas.restriction j j' hj) := by
  let n := max (large K L P i j) (large K L P i' j')
  have hn : large K L P i j ≤ n := le_max_left _ _
  have hn' : large K L P i' j' ≤ n := le_max_right _ _
  have hr := (large_ge K L P i j).trans ((AnalyticAffineSpace.radius_le_radius_iff L).2 hn)
  have hr' := (large_ge K L P i' j').trans ((AnalyticAffineSpace.radius_le_radius_iff L).2 hn')
  have h₀ := (range_chart_subset_iff K L (atlas K P) i i').1 hi
  have h₁ := (selected_range_subset_iff L (Q K L P) j j').1 hj
  have hj' : j'.val ≤ n := (le_max_right (level K L P i') j'.val).trans hn'
  let r := (S K L P).restriction i i' h₀
  let s := restriction L (Q K L P) h₁
  let t := restriction L (Q K L P) hj'
  let f := fact K L P hfixed i' j' h'
  let g := fact K L P hfixed i j h
  change r.comp f = g.comp s
  apply (represents_restriction L (Q K L P) hj').hom_ext (E K L P i)
  have hleft : f.comp t = rawPull K L P hfixed i' n hr' := fact_comp_at K L P hfixed i' j' h' hn' hr'
  have hright : g.comp (restriction L (Q K L P) (h₁.trans hj')) = rawPull K L P hfixed i n hr :=
    fact_comp_at K L P hfixed i j h hn hr
  exact (BoundedAlgHom.comp_assoc r f t).trans
    ((congrArg r.comp hleft).trans ((rawPull_sub K L P hfixed i i' h₀ n hr hr').trans
      (hright.symm.trans ((congrArg g.comp (rawRestriction_trans K L P h₁ hj').symm).trans
        (BoundedAlgHom.comp_assoc g s t).symm))))

/-- Assemble the actual strong map, with all admissible bounded pullbacks. -/
def comparison : StrongHom (src K L P) (tgt K L P) where
  baseMap := ⟨pointFun K L P hfixed, continuous_pointFun K L P hfixed⟩
  target_exists := exists_admissible K L P hfixed
  pullback i j h := fact K L P hfixed i j h
  chart_comm i j h x := fact_chart_comm K L P hfixed i j h x
  restriction_comm := fact_restriction_comm K L P hfixed

/-- Preserve the full comparison, not just the map on underlying spaces. -/
def compatibleComparison : CompatibleStrongHom (src K L P) (tgt K L P) where
  toStrongHom := comparison K L P hfixed
  compatible := (comparison K L P hfixed).hasLocallyCompatiblePullbacks_iff.mpr
    ((comparison K L P hfixed).hasCoherentPullbacks_of_hasDirectedCharts (atlas_hasDirectedCharts L (Q K L P)))

theorem comparison_isQuasiIso : (comparison K L P hfixed).IsQuasiIso := by
  refine ⟨isHomeomorph_pointFun K L P hfixed, ?_⟩
  intro i j h
  rw [← (comparison K L P hfixed).range_pullback i j h]
  exact fact_represents K L P hfixed i j h

/-- The fixed-radius chart comparison implies the strong comparison of the two
affine ground field extensions. -/
theorem reduceStrongComparison (h : AffineAnalytificationChartBaseChangeStatement.{u, u', v}) :
    AffineAnalytificationGroundFieldComparisonStatement.{u, u', v} := by
  intro K _ _ _ L _ _ _ _ A _ _ P
  exact ⟨compatibleComparison K L P h, comparison_isQuasiIso K L P h, pointFun_projection K L P h,
    fact_algebraMap K L P h⟩

end Langlands.Analytic.AffineAnalytification.GroundFieldComparison
