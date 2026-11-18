import Langlands.Geometry.Analytic.AffineAnalytificationChartFamilies
import Langlands.Geometry.Analytic.AffineAnalytificationAffinoidUniversalProof
import Langlands.Geometry.Analytic.AtlasSaturationComparison

/-! # Selected chart pullbacks for compatible algebra maps -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification.ChartFamilyComparison

open Set AffinoidAtlasPresentation PresentedAffinoidAlgebra

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
  {A : Type v} [CommRing A] [Algebra K A]

private theorem restriction_square {R R' Q Q' T : PresentedAffinoidAlgebra K}
    (s : BoundedAlgHom K R' R) (p : BoundedAlgHom K Q R) (p' : BoundedAlgHom K Q' R')
    (r : BoundedAlgHom K T Q) (r' : BoundedAlgHom K T Q')
    (a : A →ₐ[K] Q) (a' : A →ₐ[K] Q') (c : A →ₐ[K] T)
    (φ : A →ₐ[K] R) (φ' : A →ₐ[K] R')
    (hr : r.toAlgHom.comp c = a) (hr' : r'.toAlgHom.comp c = a')
    (hp : p.toAlgHom.comp a = φ) (hp' : p'.toAlgHom.comp a' = φ')
    (hφ : s.toAlgHom.comp φ' = φ)
    (gen : Fin T.arity → A) (hgen : ∀ t, coordinate K T t = c (gen t)) :
    s.comp (p'.comp r') = p.comp r := by
  have h : (s.comp (p'.comp r')).toAlgHom.comp c = (p.comp r).toAlgHom.comp c := by
    change s.toAlgHom.comp (p'.toAlgHom.comp (r'.toAlgHom.comp c)) =
      p.toAlgHom.comp (r.toAlgHom.comp c)
    rw [hr', hp', hr, hp, hφ]
  apply PresentedAffinoidAlgebra.hom_ext_coordinate
  intro t
  rw [hgen t]
  exact AlgHom.congr_fun h (gen t)

variable [CompleteSpace K] (P : FinitePolynomialPresentation K A)
  {S : AffinoidAtlasPresentation.{u, u, u} K}

private theorem affinoidPullback_comp_coordinateMap (R : PresentedAffinoidAlgebra K)
    (φ : A →ₐ[K] R) :
    (affinoidPullback K P R φ).toAlgHom.comp (coordinateMap P (affinoidIndex K P R φ)) = φ :=
  AlgHom.ext (affinoidPullback_algebraMap K P R φ)

/-- Choose a bounded target chart for every source chart and check restriction
compatibility in common upper original charts. -/
def algebraFamilyData (d : AlgebraFamily S A) :
    LocalChartMapData S (presentation K P).saturationSource where
  indexMap i := ULift.up (affinoidIndex K P (S.atlas.algebra i) (d.map i))
  pullback i := affinoidPullback K P (S.atlas.algebra i) (d.map i)
  restriction_comm i i' hi := by
    let j := affinoidIndex K P (S.atlas.algebra i) (d.map i)
    let j' := affinoidIndex K P (S.atlas.algebra i') (d.map i')
    obtain ⟨q, hq, hq'⟩ := original_hasDirectedCharts P j j'
    refine ⟨ULift.up q, hq, hq', ?_⟩
    exact restriction_square (S.atlas.restriction i i' hi)
      (affinoidPullback K P (S.atlas.algebra i) (d.map i))
      (affinoidPullback K P (S.atlas.algebra i') (d.map i'))
      ((presentation K P).atlas.restriction j q hq)
      ((presentation K P).atlas.restriction j' q hq')
      (coordinateMap P j) (coordinateMap P j') (coordinateMap P q) (d.map i) (d.map i')
      (restriction_coordinateMap P j q hq) (restriction_coordinateMap P j' q hq')
      (affinoidPullback_comp_coordinateMap P (S.atlas.algebra i) (d.map i))
      (affinoidPullback_comp_coordinateMap P (S.atlas.algebra i') (d.map i'))
      (d.naturality i i' hi) (fun t => P.map (MvPolynomial.X t))
      (AffinoidUniversalComparison.coordinate_eq_algebraMap P q.val)

/-- The selected bounded pullback recovers the supplied algebra map. -/
theorem algebraFamilyData_coordinate (d : AlgebraFamily S A) (i : S.atlas.Index) :
    ((algebraFamilyData P d).pullback i).toAlgHom.comp
      (coordinateMap P ((algebraFamilyData P d).indexMap i).down) = d.map i :=
  affinoidPullback_comp_coordinateMap P (S.atlas.algebra i) (d.map i)

end Langlands.Analytic.AffineAnalytification.ChartFamilyComparison
