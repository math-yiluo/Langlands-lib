import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionAnalyticFunctorialityStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothPureDimensionalCharts
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Analytic functoriality for all smooth dimension pieces -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Set Filter Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped ContDiff Manifold

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K]

/-- Near a point mapping into an open pure-dimensional target, the point map
has an analytic lift into that target for any admissible family. -/
private theorem exists_analytic_lift
    (σ : AnalyticPointStructure K) (hσ : σ.IsAdmissible)
    (n m : ℕ) (P Q Y : AlgebraicSpace (Spec (CommRingCat.of K)))
    (hP : IsSmoothPureDimensional K n P) (hQ : IsSmoothPureDimensional K m Q)
    (F : P ⟶ Y) (j : Q ⟶ Y) (hj : IsOpenImmersion (hom j))
    (x : RingPoints K P K) (y : RingPoints K Q K)
    (hxy : RingPoints.map F x = RingPoints.map j y) :
    letI := etaleChartTopology K P
    letI := etaleChartTopology K Q
    letI := σ.chartedSpace n P hP
    letI := σ.chartedSpace m Q hQ
    ∃ H : RingPoints K P K → RingPoints K Q K,
      ContMDiffAt 𝓘(K, Fin n → K) 𝓘(K, Fin m → K) ω H x ∧
      H x = y ∧
      ∀ᶠ z in 𝓝 x, RingPoints.map j (H z) = RingPoints.map F z := by
  let c := smoothPureDimensionalAffineChart K n P hP x
  let a := hom (c.hom ≫ F)
  let hr := hj.1
  let V := hr.pullback a
  let i := hr.snd a
  let b := hr.fst a
  have hi : _root_.AlgebraicGeometry.IsOpenImmersion i.left :=
    hj.2 a b i (hr.isPullback a)
  let := hi
  let := c.smooth
  have hV : SmoothOfRelativeDimension n V.hom := by
    rw [← Over.w i]
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (i.left ≫ c.scheme.hom))
  let := hV
  let : Smooth V.hom := SmoothOfRelativeDimension.smooth n V.hom
  let hVs : IsSmoothPureDimensional K n ((schemeToSpace _).obj V) :=
    ⟨isLocallySeparatedLocallyFiniteType_schemeToSpace V, HasAtlasProperty.of_scheme V hV⟩
  let p : (schemeToSpace _).obj V ⟶ P := (schemeToSpace _).map i ≫ c.hom
  let g : (schemeToSpace _).obj V ⟶ Q := homMk b
  have hp : IsEtaleMorphism p := by
    intro T φ hφ
    exact (hφ.comp (isEtale_map i inferInstance)).comp c.isEtale
  have hc : schemePointsMap a c.point = RingPoints.map j y := by
    change RingPoints.map F (RingPoints.map c.hom
      ((schemeRingPointsEquiv K c.scheme K).symm c.point)) = _
    rw [c.map_point]
    exact hxy
  obtain ⟨w, hwQ, hwc⟩ := exists_pullback_point j hr a hc.symm
  let v := (schemeRingPointsEquiv K V K).symm w
  have hpv : RingPoints.map p v = x := by
    change RingPoints.map c.hom
      ((schemeRingPointsEquiv K c.scheme K).symm (w ≫ i)) = x
    rw [hwc]
    exact c.map_point
  have hgv : RingPoints.map g v = y := hwQ
  have hcomm (z : RingPoints K ((schemeToSpace _).obj V) K) :
      RingPoints.map j (RingPoints.map g z) = RingPoints.map F (RingPoints.map p z) := by
    exact congrArg (fun t => t.app _ z) (hr.isPullback a).w
  let := etaleChartTopology K P
  let := etaleChartTopology K Q
  let := etaleChartTopology K ((schemeToSpace _).obj V)
  let := σ.chartedSpace n P hP
  let := σ.chartedSpace m Q hQ
  let := σ.chartedSpace n ((schemeToSpace _).obj V) hVs
  have hd := hσ.2.2.1 n _ P hVs hP p hp v
  let H := RingPoints.map g ∘ hd.localInverse
  have hH : ContMDiffAt 𝓘(K, Fin n → K) 𝓘(K, Fin m → K) ω H
      (RingPoints.map p v) := by
    apply ContMDiffAt.comp (I' := 𝓘(K, Fin n → K))
      (RingPoints.map p v)
      (hσ.2.1 n m _ Q hVs hQ g _) hd.localInverse_contMDiffAt
  have hHv : H (RingPoints.map p v) = y := by
    dsimp only [H, Function.comp_apply]
    rw [hd.localInverse_left_inv hd.localInverse_mem_target, hgv]
  have hev : ∀ᶠ z in 𝓝 (RingPoints.map p v),
      RingPoints.map j (H z) = RingPoints.map F z := by
    filter_upwards [hd.localInverse_eventuallyEq_right] with z hz
    exact (hcomm _).trans (congrArg (RingPoints.map F) hz)
  rw [hpv] at hH hHv hev
  exact ⟨H, hH, hHv, hev⟩

/-- Every morphism of smooth spaces is analytic on the original point sets for
the varying-dimensional atlases assembled from an admissible family. -/
theorem smoothSourceDimensionAnalyticFunctoriality :
    SmoothSourceDimensionAnalyticFunctorialityStatement.{u} := by
  intro K _ hK σ hσ X Y hX hY hXqs hXls hYqs hYls f
  let := etaleChartTopology K X
  let := etaleChartTopology K Y
  refine ⟨(continuous_ringPointsMap hK ⟨hYqs, hY.locallyOfFiniteType⟩ f).continuousOn, ?_⟩
  intro n m e he e' he'
  obtain ⟨c, hc, rfl⟩ := he
  obtain ⟨d, hd, rfl⟩ := he'
  let P := SmoothDimensionPieces.space hX n
  let Q := SmoothDimensionPieces.space hY m
  let hP := SmoothDimensionPieces.space_isSmoothPureDimensional hX hXqs hXls n
  let hQ := SmoothDimensionPieces.space_isSmoothPureDimensional hY hYqs hYls m
  let jP := SmoothDimensionPieces.inclusion hX n
  let jQ := SmoothDimensionPieces.inclusion hY m
  let := etaleChartTopology K P
  let := etaleChartTopology K Q
  let := σ.chartedSpace n P hP
  let := σ.chartedSpace m Q hQ
  let := hσ.1 n P hP
  let := hσ.1 m Q hQ
  intro z hz
  have hzC : z ∈ c.target := hz.1
  obtain ⟨y, hy, hxy⟩ := hz.2.2
  have hxy' : RingPoints.map (jP ≫ f) (c.symm z) = RingPoints.map jQ y :=
    hxy.symm
  obtain ⟨H, hH, hHy, hev⟩ := exists_analytic_lift σ hσ n m P Q Y hP hQ
    (jP ≫ f) jQ (SmoothDimensionPieces.inclusion_isOpenImmersion hY m)
    (c.symm z) y hxy'
  have hCan : ContMDiffAt 𝓘(K, Fin n → K) 𝓘(K, Fin n → K) ω c.symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hzC
  have hDan : ContMDiffAt 𝓘(K, Fin m → K) 𝓘(K, Fin m → K) ω d (H (c.symm z)) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hd) (hHy ▸ hy)
  have hcoord : ContMDiffAt 𝓘(K, Fin n → K) 𝓘(K, Fin m → K) ω
      (d ∘ H ∘ c.symm) z :=
    hDan.comp z (hH.comp z hCan)
  have hcoord' : ContDiffAt K ω (d ∘ H ∘ c.symm) z :=
    contMDiffAt_iff_contDiffAt.mp hcoord
  apply ContDiffAt.contDiffWithinAt
  apply hcoord'.congr_of_eventuallyEq
  have hev' : ∀ᶠ t in 𝓝 z, RingPoints.map jQ (H (c.symm t)) =
      RingPoints.map f (RingPoints.map jP (c.symm t)) :=
    (c.continuousAt_symm hzC).eventually hev
  filter_upwards [hev'] with t ht
  change (AnalyticPointStructure.liftDimensionChart hK hY hYqs m d)
    (RingPoints.map f (RingPoints.map jP (c.symm t))) = d (H (c.symm t))
  rw [← ht]
  exact OpenPartialHomeomorph.lift_openEmbedding_apply d
    (AnalyticPointStructure.dimensionPiece_isOpenEmbedding hK hY hYqs m)

end Langlands.AlgebraicGeometry.AlgebraicSpace
