import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionAnalyticUniquenessStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.DimensionPointAtlasCalculus

/-! # Uniqueness of admissible varying-dimension analytic structures -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Set Filter Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped ContDiff Manifold

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K]

namespace DimensionAnalyticStructure

/-- Analyticity of the actual identity between two supplied atlases on one space. -/
def AnalyticIdentity (Φ Ψ : DimensionAnalyticStructure K)
    (X : AlgebraicSpace (Spec (CommRingCat.of K))) (hX : SmoothOverBase X)
    (hqs : IsQuasiSeparated X) (hls : IsLocallySeparated X) : Prop :=
  (Φ.atlas X hX hqs hls).AnalyticMap (Ψ.atlas X hX hqs hls) id

/-- Affine normalization forces agreement on polynomial affine space. -/
theorem analyticIdentity_affineSpace (Φ Ψ : DimensionAnalyticStructure K)
    (hΦ : Φ.IsAdmissible) (hΨ : Ψ.IsAdmissible) (n : ℕ) :
    Φ.AnalyticIdentity Ψ _ (affineSpace_smoothOverBase n)
      (affineSpace_isQuasiSeparated n) (affineSpace_isLocallySeparated n) := by
  obtain ⟨c, hc, hca, _⟩ := hΦ.2.2.2 n
  obtain ⟨d, hd, _, hdi⟩ := hΨ.2.2.2 n
  have heq : (d.symm ∘ c) = id := by
    funext x
    apply d.injective
    change d (d.symm (c x)) = d x
    rw [d.apply_symm_apply]
    exact (hc x).trans (hd x).symm
  unfold AnalyticIdentity
  rw [← heq]
  exact DimensionPointAtlas.analyticMap_comp_model hca hdi

/-- Agreement pulls back through an étale map, using an inverse branch for Ψ. -/
theorem analyticIdentity_of_etale_to (Φ Ψ : DimensionAnalyticStructure K)
    (hΦ : Φ.IsAdmissible) (hΨ : Ψ.IsAdmissible)
    (X Y : AlgebraicSpace (Spec (CommRingCat.of K)))
    (hX : SmoothOverBase X) (hY : SmoothOverBase Y)
    (hXqs : IsQuasiSeparated X) (hXls : IsLocallySeparated X)
    (hYqs : IsQuasiSeparated Y) (hYls : IsLocallySeparated Y)
    (f : X ⟶ Y) (hf : IsEtaleMorphism f)
    (h : Φ.AnalyticIdentity Ψ Y hY hYqs hYls) :
    Φ.AnalyticIdentity Ψ X hX hXqs hXls := by
  let := etaleChartTopology K X
  let := etaleChartTopology K Y
  apply DimensionPointAtlas.analyticMap_of_analyticAt
  intro x
  let F := RingPoints.map (A := K) f
  have hF := (hΦ.2.1 X Y hX hY hXqs hXls hYqs hYls f).analyticAt x
  have hcomp := (h.analyticAt (F x)).comp hF
  obtain ⟨e, hx, he, _, hei⟩ :=
    (hΨ.2.2.1 X Y hX hY hXqs hXls hYqs hYls f hf).2 x
  change Set.EqOn e F e.source at he
  have hfx : F x ∈ e.target := by
    rw [← he hx]
    exact e.map_source hx
  have hi := (hei.analyticAt e.open_target hfx).comp hcomp
  apply hi.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  change y = e.symm (F y)
  rw [← he hy, e.left_inv hy]

/-- Agreement descends to the image of an étale source, using a Φ inverse branch. -/
theorem analyticIdentityAt_of_etale_from (Φ Ψ : DimensionAnalyticStructure K)
    (hΦ : Φ.IsAdmissible) (hΨ : Ψ.IsAdmissible)
    (U X : AlgebraicSpace (Spec (CommRingCat.of K)))
    (hU : SmoothOverBase U) (hX : SmoothOverBase X)
    (hUqs : IsQuasiSeparated U) (hUls : IsLocallySeparated U)
    (hXqs : IsQuasiSeparated X) (hXls : IsLocallySeparated X)
    (f : U ⟶ X) (hf : IsEtaleMorphism f)
    (h : Φ.AnalyticIdentity Ψ U hU hUqs hUls) (u : RingPoints K U K) :
    (Φ.atlas X hX hXqs hXls).AnalyticAt (Ψ.atlas X hX hXqs hXls) id
      (RingPoints.map (A := K) f u) := by
  let := etaleChartTopology K U
  let := etaleChartTopology K X
  let F := RingPoints.map (A := K) f
  obtain ⟨e, hu, he, _, hei⟩ :=
    (hΦ.2.2.1 U X hU hX hUqs hUls hXqs hXls f hf).2 u
  change Set.EqOn e F e.source at he
  have hfu : F u ∈ e.target := by
    rw [← he hu]
    exact e.map_source hu
  have hleft : e.symm (F u) = u := by rw [← he hu, e.left_inv hu]
  have hident := h.analyticAt u
  have hident' := hleft.symm ▸ hident
  have hcomp := hident'.comp (hei.analyticAt e.open_target hfu)
  have hF := (hΨ.2.1 U X hU hX hUqs hUls hXqs hXls f).analyticAt u
  have hF' := hleft.symm ▸ hF
  have hfinal := hF'.comp hcomp
  apply hfinal.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hfu] with y hy
  change y = F (e.symm y)
  rw [← he (e.map_target hy), e.right_inv hy]

/-- Standard-smooth affine schemes inherit agreement from affine space. -/
theorem analyticIdentity_standardSmooth (Φ Ψ : DimensionAnalyticStructure K)
    (hΦ : Φ.IsAdmissible) (hΨ : Ψ.IsAdmissible) (n : ℕ)
    (U : Over (Spec (CommRingCat.of K))) [IsAffine U.left]
    [Algebra.IsStandardSmoothOfRelativeDimension n K (AffineCoordinateRing K U)]
    (hU : SmoothOverBase ((schemeToSpace _).obj U))
    (hUqs : IsQuasiSeparated ((schemeToSpace _).obj U))
    (hUls : IsLocallySeparated ((schemeToSpace _).obj U)) :
    Φ.AnalyticIdentity Ψ _ hU hUqs hUls := by
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n K
      (AffineCoordinateRing K U)
  let j : U ⟶ affineSpaceOver K n := (affineSchemeOverIso K U).hom ≫ ringTestMap K g
  have hj : Etale j.left := by
    let : Etale (ringTestMap K g).left :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).2 hg
    dsimp only [j, Over.comp_left]
    infer_instance
  have hf : IsEtaleMorphism ((schemeToSpace _).map j) :=
    fun _ _ hφ => hφ.comp (isEtale_map j hj)
  exact analyticIdentity_of_etale_to Φ Ψ hΦ hΨ _ _ hU
    (affineSpace_smoothOverBase n) hUqs hUls
    (affineSpace_isQuasiSeparated n) (affineSpace_isLocallySeparated n)
    ((schemeToSpace _).map j) hf (analyticIdentity_affineSpace Φ Ψ hΦ hΨ n)

/-- The identity is analytic on every smooth space in the varying-dimension family. -/
theorem analyticIdentity (Φ Ψ : DimensionAnalyticStructure K)
    (hΦ : Φ.IsAdmissible) (hΨ : Ψ.IsAdmissible)
    (X : AlgebraicSpace (Spec (CommRingCat.of K))) (hX : SmoothOverBase X)
    (hqs : IsQuasiSeparated X) (hls : IsLocallySeparated X) :
    Φ.AnalyticIdentity Ψ X hX hqs hls := by
  let := etaleChartTopology K X
  apply DimensionPointAtlas.analyticMap_of_analyticAt
  intro x
  let n := SmoothDimensionPieces.fieldPointDimension hX x
  let Y := SmoothDimensionPieces.space hX n
  let hY := SmoothDimensionPieces.space_isSmoothPureDimensional hX hqs hls n
  let c := smoothPureDimensionalAffineChart K n Y hY
    (SmoothDimensionPieces.fieldPointFactor hX x)
  let := c.isAffine
  let := c.smooth
  obtain ⟨f, hf, hss⟩ := PointManifold.General.exists_standardSmooth_basicOpen K c.scheme n
    (c.point.left (IsLocalRing.closedPoint K))
  let D := c.scheme.left.basicOpen (U := ⊤) f
  let : IsAffine D := (isAffineOpen_top c.scheme.left).basicOpen f
  let V := openOver K c.scheme D
  let i : V ⟶ c.scheme := openOverι K c.scheme D
  have hV : SmoothOfRelativeDimension n V.hom := by
    change SmoothOfRelativeDimension n (D.ι ≫ c.scheme.hom)
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (D.ι ≫ c.scheme.hom))
  let hVp := isSmoothPureDimensional_scheme n V hV
  let hVs := SmoothOverBase.of_scheme V (SmoothOfRelativeDimension.smooth n V.hom)
  let := hss
  have hident := analyticIdentity_standardSmooth Φ Ψ hΦ hΨ n V hVs
    hVp.1.1.1 hVp.1.2
  let v : RingPoint K V K := openPointLift K c.scheme K D c.point
    ((range_subset_open_iff_closedPoint K c.scheme K D c.point).2 hf)
  let G : (schemeToSpace _).obj V ⟶ Y := (schemeToSpace _).map i ≫ c.hom
  let F : (schemeToSpace _).obj V ⟶ X := G ≫ SmoothDimensionPieces.inclusion hX n
  have hiEt : Etale i.left := by
    change Etale D.ι
    infer_instance
  have hF : IsEtaleMorphism F := by
    intro T φ hφ
    exact ((hφ.comp (isEtale_map i hiEt)).comp c.isEtale).comp
      (PointOpenSubspace.isEtale_of_isOpenImmersion
        (SmoothDimensionPieces.inclusion_isOpenImmersion hX n))
  have hv : RingPoints.map F ((schemeRingPointsEquiv K V K).symm v) = x := by
    have hi : RingPoints.map ((schemeToSpace _).map i)
        ((schemeRingPointsEquiv K V K).symm v) =
        (schemeRingPointsEquiv K c.scheme K).symm c.point := by
      apply (schemeRingPointsEquiv K c.scheme K).injective
      change openPointMap K c.scheme K D v = c.point
      exact openPointMap_lift K c.scheme K D c.point _
    simp only [F, G, RingPoints.map_comp]
    rw [hi, c.map_point]
    exact SmoothDimensionPieces.fieldPointFactor_map hX x
  have h := analyticIdentityAt_of_etale_from Φ Ψ hΦ hΨ _ X hVs hX
    hVp.1.1.1 hVp.1.2 hqs hls F hF hident ((schemeRingPointsEquiv K V K).symm v)
  rw [hv] at h
  exact h

/-- Any two admissible varying-dimension families induce the same analytic structure. -/
theorem equivalent_of_isAdmissible (Φ Ψ : DimensionAnalyticStructure K)
    (hΦ : Φ.IsAdmissible) (hΨ : Ψ.IsAdmissible) : Φ.Equivalent Ψ := by
  intro X hX hqs hls
  exact ⟨analyticIdentity Φ Ψ hΦ hΨ X hX hqs hls,
    analyticIdentity Ψ Φ hΨ hΦ X hX hqs hls⟩

end DimensionAnalyticStructure

/-- Exact-target uniqueness in every universe, without completeness assumptions. -/
theorem smoothSourceDimensionAnalyticUniqueness :
    SmoothSourceDimensionAnalyticUniquenessStatement.{u} := by
  intro K _ Φ Ψ hΦ hΨ
  exact DimensionAnalyticStructure.equivalent_of_isAdmissible Φ Ψ hΦ hΨ

end Langlands.AlgebraicGeometry.AlgebraicSpace
