import Langlands.Geometry.Analytic.CompleteAnalyticExtensionPointEmbeddingStatement
import Langlands.Geometry.Analytic.GroundFieldRationalLocusProof
import Langlands.Geometry.Analytic.SpaceAnalytificationFieldPointsProof
import Langlands.Geometry.Analytic.SpaceAnalytificationRationalPointsProof
import Langlands.Geometry.Analytic.AffineAnalytificationBaseChangeProof
import Langlands.Geometry.Analytic.AffineAnalytificationRationalPointNaturalityProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteExtensionPointEmbeddingReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianExtensionClosedReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.CompleteExtensionPointClosedRangeProof
import Mathlib.Analysis.Normed.Algebra.Ultra

/-! # Proof of the analytic comparison for extension of rational points

This file proves `CompleteAnalyticExtensionPointEmbeddingStatement`, following the last
paragraph of the proof of Conrad's Proposition 5.11(3). The ground-field comparison of
analytifications identifies the projection of the analytic point of `x_L` with the
analytic point of `x`. The rational-point topology comparison gives the embedding, and the
closed rational locus of the scalar-extended affinoid atlas gives closed range. The file
also derives `HenselianExtensionPointEmbeddingStatement` from analytification existence and
the ground-field comparison. -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory SaturatedAtlasPresentation Set Topology
open AffinoidAtlasPresentation.GroundFieldExtension (localizedFunctor localizedProjection)
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology (AlgPoint)
open scoped TensorProduct

/-- The analytic points of the `K`-points of `X` are exactly the `K`-rational points of the
presentation underlying an analytification. -/
private theorem range_rationalPoint
    {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hs : IsSeparated X)
    (hft : LocallyOfFiniteTypeOverBase X)
    {Y : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}
    (hp : IsAnalytification K X Y p) (P : FinitePolynomialPresentation K K) :
    range (rationalPoint p P) = (localizedObjectEquiv.symm Y).presentation.rationalLocus K := by
  obtain ⟨e, he⟩ := (spaceAnalytificationFieldPoints K X hs hft Y p hp).2 P
  obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective Y
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, he x⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨x, (he x).symm⟩

/-- Saturating an affinoid atlas presentation does not change its rational locus. -/
private theorem rationalLocus_saturation
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : AffinoidAtlasPresentation.{u, u, u} K) :
    A.saturatedPresentation.rationalLocus K = A.rationalLocus K := by
  let e := FieldPointSaturationComparison.saturationEquiv A
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨e.symm q, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨e p, rfl⟩

variable {K L : Type u}
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}

open AffineAnalytification AffineAnalytification.BaseChangeComparison in
/-- The ground-field comparison gives an analytification of `X_L` on `Y_L` for which the
scalar projection sends the analytic point of `x_L` to the analytic point of `x`. -/
private theorem projection_rationalPoint_extension (h : SpaceAnalytificationGroundFieldStatement.{u})
    (hs : IsSeparated X) (hft : LocallyOfFiniteTypeOverBase X)
    {Y : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}
    (hp : IsAnalytification K X Y p) :
    let XL := baseChange (Spec.algebraMap K L) X
    let F := localizedFunctor.{u, u, u, u} K L
    ∃ q : PointFamily L XL (F.obj Y), IsAnalytification L XL (F.obj Y) q ∧
      ∀ (P : FinitePolynomialPresentation K K) (Q : FinitePolynomialPresentation L L)
        (x : RingPoints K X K),
        ((localizedProjection K L).app Y
          (ULift.up (rationalPoint q Q (extensionPointMap L X x)))).down =
          rationalPoint p P x := by
  obtain ⟨q, hq, htests⟩ := h K L X hs hft Y p hp
  refine ⟨q, hq, ?_⟩
  intro P Q x
  obtain ⟨c, hproj, hc⟩ := htests K P
  let T := L ⊗[K] K
  let R := baseChangePresentation K L P
  let xT := (baseChangeRingPointsEquiv K L T X).symm
    (RingPoints.changeRing Algebra.TensorProduct.includeRight x)
  let idK := AlgPoint.ofAlgHom (AlgHom.id K K)
  let idL := AlgPoint.ofAlgHom (AlgHom.id L L)
  let φ := rationalLift K L idK
  have hcomp : (φ.restrictScalars K).comp Algebra.TensorProduct.includeRight =
      Algebra.ofId K L :=
    AlgHom.ext fun b => (rationalLift_tmul K L idK 1 b).trans (one_mul _)
  have hφ : RingPoints.changeRing φ xT = extensionPointMap L X x := by
    apply (baseChangeRingPointsEquiv K L L X).injective
    rw [baseChangeRingPointsEquiv_changeRing, extensionPointMap]
    change RingPoints.changeRing (φ.restrictScalars K)
      (baseChangeRingPointsEquiv K L T X ((baseChangeRingPointsEquiv K L T X).symm
        (RingPoints.changeRing Algebra.TensorProduct.includeRight x))) = _
    simp only [Equiv.apply_symm_apply, RingPoints.changeRing_comp, hcomp]
  have han :
      localizedSpaceFunctor.map (localizedHom L R Q φ) (analyticPoint L Q idL) =
        analyticPoint L R (AlgPoint.ofAlgHom φ) := by
    rw [localizedSpaceFunctor_map_localizedHom]
    exact affineAnalytificationRationalPointNaturality L T L R Q φ idL
  have heq : q T R xT = c.inv ≫ (localizedFunctor K L).map (p K P x) := by
    rw [← hc x, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let z := analyticPoint L R (AlgPoint.ofAlgHom φ)
  have hqz :
      rationalPoint q Q (extensionPointMap L X x) =
        localizedSpaceFunctor.map ((localizedFunctor K L).map (p K P x))
          (localizedSpaceFunctor.map c.inv z) := by
    unfold rationalPoint
    rw [← hφ, hq.naturality R Q φ xT, Functor.map_comp]
    change localizedSpaceFunctor.map (q T R xT)
      (localizedSpaceFunctor.map (localizedHom L R Q φ) (analyticPoint L Q idL)) = _
    rw [han, heq, Functor.map_comp]
    rfl
  rw [hqz]
  have hn := congrArg (fun k => (k (ULift.up (localizedSpaceFunctor.map c.inv z))).down)
    ((localizedProjection K L).naturality (p K P x))
  exact hn.trans (congrArg (localizedSpaceFunctor.map (p K P x))
    ((hproj z).trans (baseChangeMap_analyticPoint K L P idK)))

/-- Use the actual analytification comparison and the closed locus on the analytic
scalar extension to identify the algebraic map and prove closed embedding. -/
theorem completeAnalyticExtensionPointEmbedding :
    CompleteAnalyticExtensionPointEmbeddingStatement.{u} := by
  intro h K L _ _ _ _ _ _ _ X hs hft Y p hp
  obtain ⟨q, hq, hcomm⟩ := projection_rationalPoint_extension (L := L) h hs hft hp
  refine ⟨q, hq, hcomm, ?_⟩
  let XL := baseChange (Spec.algebraMap K L) X
  have hsL : IsSeparated XL := hs.baseChange
  have hftL : LocallyOfFiniteTypeOverBase XL := hft.baseChange
  let P := FinitePolynomialPresentation.ofFiniteType K K
  let Q := FinitePolynomialPresentation.ofFiniteType L L
  let F := localizedFunctor.{u, u, u, u} K L
  let π : localizedSpaceFunctor.obj (F.obj Y) → localizedSpaceFunctor.obj Y :=
    fun z => ((localizedProjection K L).app Y (ULift.up z)).down
  have hπ : Continuous π :=
    continuous_uliftDown.comp (((localizedProjection K L).app Y).hom.continuous.comp
      continuous_uliftUp)
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints L XL L) := etaleChartTopology L XL
  let g := rationalPoint q Q
  have hg : IsEmbedding g :=
    (spaceAnalytificationRationalPoints L XL hsL hftL (F.obj Y) q hq).2 Q
  have he : IsEmbedding (extensionPointMap L X) := by
    refine IsEmbedding.of_comp (continuous_extensionPointMap (X := X) L) (hπ.comp hg.continuous) ?_
    have hfun : (π ∘ g) ∘ extensionPointMap L X = rationalPoint p P := funext (hcomm P Q)
    rw [hfun]
    exact (spaceAnalytificationRationalPoints K X hs hft Y p hp).2 P
  refine ⟨he, ?_⟩
  obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective Y
  let T := IndexedAffinoidAtlas.GroundFieldExtension.presentation K L A.presentation.atlas
  let S := A.presentation.rationalLocus K
  let R := T.rationalLocus L
  obtain ⟨hc, hi, _⟩ :=
    IndexedAffinoidAtlas.GroundFieldExtension.groundFieldRationalLocus K L A.presentation
  have hfRange : range (rationalPoint p P) = S := range_rationalPoint hs hft hp P
  have hgRange : range g = R :=
    (range_rationalPoint hsL hftL hq Q).trans (rationalLocus_saturation T)
  let gR : RingPoints L XL L → R :=
    fun y => ⟨g y, hgRange ▸ mem_range_self y⟩
  have hmem (x : RingPoints K X K) : π (g (extensionPointMap L X x)) ∈ S :=
    (congrArg (fun z : A.presentation.space => z ∈ S) (hcomm P Q x)).mpr
      (hfRange ▸ mem_range_self x)
  have hRange : range (extensionPointMap L X) = gR ⁻¹' (Subtype.val ⁻¹' (π ⁻¹' S)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact hmem x
    · intro hy
      have hy' : π (g y) ∈ range (rationalPoint p P) := hfRange.symm ▸ hy
      obtain ⟨x, hx⟩ := hy'
      exact ⟨x, hg.injective (hi ⟨(gR _).property, hmem x⟩ ⟨(gR y).property, hy⟩
        ((hcomm P Q x).trans hx))⟩
  have hClosed : IsClosed (Subtype.val ⁻¹' (π ⁻¹' S) : Set R) := hc
  have hgR : Continuous gR := hg.continuous.subtype_mk _
  exact hRange.symm ▸ hClosed.preimage hgR

/-- Analytification and its scalar comparison supply the nonarchimedean
complete-field case of the henselian extension embedding theorem. -/
theorem henselianExtensionPointEmbedding_of_analytification
    (hexists : SpaceAnalytificationExistenceStatement.{u})
    (hbase : SpaceAnalytificationGroundFieldStatement.{u}) :
    HenselianExtensionPointEmbeddingStatement.{u} := by
  apply ExtensionClosedReduction.henselianExtensionPointEmbedding_of_complete
  intro K L _ _ _ _ _ X hX hs
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  by_cases hK : IsUltrametricDist K
  · let := hK
    let : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    obtain ⟨Y, p, hp⟩ := hexists K X hs hX.2
    obtain ⟨_, _, _, hclosed⟩ :=
      completeAnalyticExtensionPointEmbedding hbase K L X hs hX.2 Y p hp
    exact hclosed.isClosed_range
  · exact CompleteExtensionClosedRange.completeExtensionPointClosedRange K L X hX hs

end Langlands.Analytic.SpaceAnalytification
