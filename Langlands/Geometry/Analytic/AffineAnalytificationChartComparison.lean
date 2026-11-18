import Langlands.Geometry.Analytic.AffineAnalytificationChartFamilies
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityProof

/-! # Faithfulness and composition of chart-family extraction -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification.ChartFamilyComparison

open CategoryTheory Set AffinoidAtlasPresentation PresentedAffinoidAlgebra

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
  {S : SaturatedAtlasPresentation.{u, u, u} K}

/-- Coordinate extraction can be computed using any admissible original chart. -/
theorem toAlgebraFamily_map_eq (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index)
    (j : (presentation K P).atlas.Index)
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j)) :
    (toAlgebraFamily P F).map i = chartAlgHom P F i j h :=
  chartAlgHom_independent P F i (selectedTarget P F i) j
    (selectedTarget_spec P F i) h

omit [CompleteSpace K] in
private theorem bounded_eq_of_coordinateMap_eq {R T : PresentedAffinoidAlgebra K}
    (a : A →ₐ[K] R) (p q : BoundedAlgHom K R T) (c : Fin R.arity → A)
    (hc : ∀ t, coordinate K R t = a (c t))
    (h : p.toAlgHom.comp a = q.toAlgHom.comp a) : p = q := by
  apply PresentedAffinoidAlgebra.hom_ext_coordinate
  intro t
  rw [hc t]
  exact AlgHom.congr_fun h (c t)

/-- Pullbacks from the same original target agree if their coordinate-algebra maps agree. -/
theorem originalPullback_eq_of_chartAlgHom_eq (F G : S ⟶ saturated K P)
    (i : S.presentation.atlas.Index) (j : (presentation K P).atlas.Index)
    (hF : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j))
    (hG : G.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j))
    (h : chartAlgHom P F i j hF = chartAlgHom P G i j hG) :
    originalPullback P F i j hF = originalPullback P G i j hG :=
  bounded_eq_of_coordinateMap_eq (coordinateMap P j) (originalPullback P F i j hF)
    (originalPullback P G i j hG) (fun t => P.map (MvPolynomial.X t))
    (LocalizedFunctorialityComparison.OriginalStrongMaps.coordinate_eq_algebraMap P j.val) h

omit [CompleteSpace K] in
private theorem comp_algebraCast_cancel {R R' T : PresentedAffinoidAlgebra K}
    (h : R = R') (f : BoundedAlgHom K R T) (g : BoundedAlgHom K R T)
    (e : f.comp (algebraCast h.symm) = g.comp (algebraCast h.symm)) : f = g := by
  have he := congrArg (fun p : BoundedAlgHom K R' T => p.comp (algebraCast h)) e
  simpa only [BoundedAlgHom.comp_assoc, algebraCast_comp_symm, BoundedAlgHom.comp_id] using he

/-- The algebra maps on the source charts determine the complete strong morphism. -/
theorem toAlgebraFamily_ext (F G : S ⟶ saturated K P)
    (h : ∀ i, (toAlgebraFamily P F).map i = (toAlgebraFamily P G).map i) : F = G := by
  have hpb : ∀ i, ∃ (q : (presentation K P).atlas.Index)
      (hF : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
        range ((presentation K P).atlas.chart q))
      (hG : G.baseMap '' range (S.presentation.atlas.chart i) ⊆
        range ((presentation K P).atlas.chart q)),
      F.pullback i (originalIndex P q) (original_admissible P F i q hF) =
        G.pullback i (originalIndex P q) (original_admissible P G i q hG) := by
    intro i
    obtain ⟨j, hj⟩ := original_target_exists P F i
    obtain ⟨k, hk⟩ := original_target_exists P G i
    obtain ⟨q, hjq, hkq⟩ := original_hasDirectedCharts P j k
    have hF := hj.trans hjq
    have hG := hk.trans hkq
    have e := (toAlgebraFamily_map_eq P F i q hF).symm.trans
      ((h i).trans (toAlgebraFamily_map_eq P G i q hG))
    exact ⟨q, hF, hG, comp_algebraCast_cancel (originalAlgebra P q) _ _
      (originalPullback_eq_of_chartAlgHom_eq P F G i q hF hG e)⟩
  choose q hF hG heq using hpb
  let hd := saturated_hasDirectedCharts P
  let d := F.toLocalChartMapData hd (fun i => originalIndex P (q i))
    (fun i => original_admissible P F i (q i) (hF i))
  have hf : d.RealizedBy F :=
    F.toLocalChartMapData_realizedBy hd _ _
  have hg : d.RealizedBy G :=
    fun i => ⟨original_admissible P G i (q i) (hG i), (heq i).symm⟩
  exact (hf.eq_toStrongHom hd).trans (hg.eq_toStrongHom hd).symm

/-- Extraction of the compatible algebra family is injective. -/
theorem toAlgebraFamily_injective :
    Function.Injective (fun F : S ⟶ saturated K P => toAlgebraFamily P F) := by
  intro F G h
  exact toAlgebraFamily_ext P F G (fun i => congrArg (fun a : AlgebraFamily S.presentation A =>
    a.map i) h)

variable {B : Type w} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

omit [CompleteSpace K] in
private theorem comp_cast_square {R R' T T' U : PresentedAffinoidAlgebra K}
    (r : BoundedAlgHom K R' R) (t : BoundedAlgHom K T' T)
    (a : BoundedAlgHom K R U) (b : BoundedAlgHom K T R)
    (c : BoundedAlgHom K T U) (d : BoundedAlgHom K T' R')
    (hc : c = a.comp b) (hb : b.comp t = r.comp d) :
    c.comp t = (a.comp r).comp d := by
  rw [hc, BoundedAlgHom.comp_assoc, hb, ← BoundedAlgHom.comp_assoc]

omit [CompleteSpace K] in
private theorem comp_coordinate {R T U : PresentedAffinoidAlgebra K}
    (p : BoundedAlgHom K R U) (q : BoundedAlgHom K T R) (r : BoundedAlgHom K T U)
    (a : A →ₐ[K] T) (b : B →ₐ[K] R) (f : A →ₐ[K] B)
    (hr : r = p.comp q) (hq : q.toAlgHom.comp a = b.comp f) :
    r.toAlgHom.comp a = (p.toAlgHom.comp b).comp f := by
  rw [hr]
  exact congrArg (fun g : A →ₐ[K] R => p.toAlgHom.comp g) hq

/-- Postcomposition by an induced affine morphism precomposes each algebra map. -/
theorem toAlgebraFamily_comp_saturatedHom (F : S ⟶ saturated K Q)
    (i : S.presentation.atlas.Index) :
    (toAlgebraFamily P (F ≫ saturatedHom K P Q f)).map i =
      ((toAlgebraFamily Q F).map i).comp f := by
  let G := saturatedHom K P Q f
  obtain ⟨j, hj⟩ := original_target_exists Q F i
  obtain ⟨k, hk⟩ := (strongHom K P Q f).target_exists j
  have hG : G.baseMap '' range ((saturated K Q).presentation.atlas.chart (originalIndex Q j)) ⊆
      range ((saturated K P).presentation.atlas.chart (originalIndex P k)) := by
    rw [originalRange, originalRange]
    exact hk
  have hF := original_admissible Q F i j hj
  have hFG := F.comp_admissible G i (originalIndex Q j) (originalIndex P k) hF hG
  have h : (F ≫ G).baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart k) :=
    hFG.trans (originalRange P k).subset
  have heq : HEq (G.pullback (originalIndex Q j) (originalIndex P k) hG)
      ((strongHom K P Q f).pullback j k hk) :=
    (strongHom K P Q f).saturationExtension_pullback_original
      (strongHom_hasCoherentPullbacks K P Q f) j k hk
  have hcast := (algebraCast_square (originalAlgebra Q j).symm (originalAlgebra P k).symm
    heq.symm).symm
  have hcomp : (F ≫ G).pullback i (originalIndex P k) hFG =
      (F.pullback i (originalIndex Q j) hF).comp
        (G.pullback (originalIndex Q j) (originalIndex P k) hG) :=
    F.saturatedComp_pullback G S.hasAllLocalDomains (saturated K Q).hasAllLocalDomains
      i (originalIndex Q j) (originalIndex P k) hF hG hFG
  have hb := comp_cast_square (algebraCast (originalAlgebra Q j).symm)
    (algebraCast (originalAlgebra P k).symm) (F.pullback i (originalIndex Q j) hF)
    (G.pullback (originalIndex Q j) (originalIndex P k) hG)
    ((F ≫ G).pullback i (originalIndex P k) hFG) ((strongHom K P Q f).pullback j k hk)
    hcomp hcast
  have hc : ((strongHom K P Q f).pullback j k hk).toAlgHom.comp (coordinateMap P k) =
      (coordinateMap Q j).comp f :=
    AlgHom.ext
      (LocalizedFunctorialityComparison.OriginalStrongMaps.strongHom_pullback_algebraMap
        P Q f j k hk)
  calc
    (toAlgebraFamily P (F ≫ G)).map i = chartAlgHom P (F ≫ G) i k h :=
      toAlgebraFamily_map_eq P (F ≫ G) i k h
    _ = (chartAlgHom Q F i j hj).comp f :=
      comp_coordinate (originalPullback Q F i j hj) ((strongHom K P Q f).pullback j k hk)
        (originalPullback P (F ≫ G) i k h) (coordinateMap P k) (coordinateMap Q j) f hb hc
    _ = ((toAlgebraFamily Q F).map i).comp f :=
      congrArg (fun g : B →ₐ[K] S.presentation.atlas.algebra i => g.comp f)
        (toAlgebraFamily_map_eq Q F i j hj).symm

end Langlands.Analytic.AffineAnalytification.ChartFamilyComparison
