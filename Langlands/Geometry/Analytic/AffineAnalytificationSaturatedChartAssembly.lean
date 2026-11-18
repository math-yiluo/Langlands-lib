import Langlands.Geometry.Analytic.AffineAnalytificationChartComparison
import Langlands.Geometry.Analytic.AtlasSaturationComparison

/-! # From original chart data to a saturated strong morphism -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification.ChartFamilyComparison

open CategoryTheory Set AffinoidAtlasPresentation

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]

private theorem transport_restriction_comm
    {R R' T T' Q Q' U V : PresentedAffinoidAlgebra K}
    (r : BoundedAlgHom K R' R) (t : BoundedAlgHom K T' T) (q : BoundedAlgHom K Q' Q)
    (a : BoundedAlgHom K R U) (b : BoundedAlgHom K T V) (s : BoundedAlgHom K V U)
    (f : BoundedAlgHom K Q R) (g : BoundedAlgHom K Q T)
    (f' : BoundedAlgHom K Q' R') (g' : BoundedAlgHom K Q' T')
    (hf : r.comp f' = f.comp q) (hg : t.comp g' = g.comp q)
    (h : s.comp (b.comp g) = a.comp f) :
    s.comp ((b.comp t).comp g') = (a.comp r).comp f' := by
  calc
    s.comp ((b.comp t).comp g') = s.comp ((b.comp g).comp q) := by
      rw [BoundedAlgHom.comp_assoc b t g', hg, ← BoundedAlgHom.comp_assoc b g q]
    _ = (s.comp (b.comp g)).comp q := (BoundedAlgHom.comp_assoc _ _ _).symm
    _ = (a.comp f).comp q := congrArg (fun l : BoundedAlgHom K Q U => l.comp q) h
    _ = (a.comp r).comp f' := by
      rw [BoundedAlgHom.comp_assoc a r f', hf, ← BoundedAlgHom.comp_assoc a f q]

private theorem recover_coordinate {R R' T : PresentedAffinoidAlgebra K}
    {A : Type v} [CommRing A] [Algebra K A] (e : R' = R)
    (p : BoundedAlgHom K R T) (p' : BoundedAlgHom K R' T) (a : A →ₐ[K] R)
    (h : p' = p.comp (algebraCast e)) :
    (p'.comp (algebraCast e.symm)).toAlgHom.comp a = p.toAlgHom.comp a := by
  rw [h, BoundedAlgHom.comp_assoc, algebraCast_comp_symm, BoundedAlgHom.comp_id]

variable [CompleteSpace K] {A : Type v} [CommRing A] [Algebra K A]
  (P : FinitePolynomialPresentation K A) {S : SaturatedAtlasPresentation.{u, u, u} K}

/-- Transport local maps into the universe-reindexed original polynomial charts
to local maps into the corresponding charts of the saturated presentation. -/
def saturatedChartData
    (d : LocalChartMapData S.presentation (presentation K P).saturationSource) :
    LocalChartMapData S.presentation (saturated K P).presentation where
  indexMap i := originalIndex P (d.indexMap i).down
  pullback i := (d.pullback i).comp (algebraCast (originalAlgebra P (d.indexMap i).down))
  restriction_comm i i' hi := by
    obtain ⟨q, h, h', hc⟩ := d.restriction_comm i i' hi
    let j := (d.indexMap i).down
    let j' := (d.indexMap i').down
    let k := q.down
    have hsat := originalSubset P j k h
    have hsat' := originalSubset P j' k h'
    refine ⟨originalIndex P k, hsat, hsat', ?_⟩
    have hcast := algebraCast_square (originalAlgebra P j) (originalAlgebra P k)
      ((presentation K P).atlas.saturatedAtlas_original_restriction_heq j k h hsat)
    have hcast' := algebraCast_square (originalAlgebra P j') (originalAlgebra P k)
      ((presentation K P).atlas.saturatedAtlas_original_restriction_heq j' k h' hsat')
    exact transport_restriction_comm _ _ _ (d.pullback i) (d.pullback i')
      (S.presentation.atlas.restriction i i' hi) _ _ _ _ hcast hcast' hc

/-- Assemble the transported data into a complete strong morphism. -/
def saturatedChartHom
    (d : LocalChartMapData S.presentation (presentation K P).saturationSource) :
    S ⟶ saturated K P :=
  (saturatedChartData P d).toStrongHom (saturated_hasDirectedCharts P)

/-- Extraction after saturated chart assembly reads the supplied coordinate maps. -/
theorem toAlgebraFamily_saturatedChartHom
    (d : LocalChartMapData S.presentation (presentation K P).saturationSource)
    (i : S.presentation.atlas.Index) :
    (toAlgebraFamily P (saturatedChartHom P d)).map i =
      (d.pullback i).toAlgHom.comp (coordinateMap P (d.indexMap i).down) := by
  let j := (d.indexMap i).down
  let D := saturatedChartData P d
  let F := saturatedChartHom P d
  have h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j) :=
    (D.image_chart_subset i).trans (originalRange P j).subset
  have hpull : F.pullback i (originalIndex P j) (original_admissible P F i j h) =
      (d.pullback i).comp (algebraCast (originalAlgebra P j)) :=
    D.toStrongHom_pullback_selected (saturated_hasDirectedCharts P) i
  exact (toAlgebraFamily_map_eq P F i j h).trans
    (recover_coordinate (originalAlgebra P j) (d.pullback i) _ (coordinateMap P j) hpull)

end Langlands.Analytic.AffineAnalytification.ChartFamilyComparison
