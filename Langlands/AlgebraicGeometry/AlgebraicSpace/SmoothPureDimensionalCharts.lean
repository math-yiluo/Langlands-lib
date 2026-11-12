import Langlands.AlgebraicGeometry.AlgebraicSpace.AnalyticPointManifold
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyUniqueness
import Langlands.AlgebraicGeometry.SmoothFieldRelativeDimensionDescent
import Langlands.AlgebraicGeometry.PointManifold.Analytic.SmoothAffineManifold
import Langlands.AlgebraicGeometry.PointTopology.CompleteHenselianValuedFieldProof

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped ContDiff Manifold

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The relative-dimension property of one good atlas holds on every etale scheme chart. -/
theorem smoothRelativeDimension_of_isEtale
    {k : Type u} [Field k] {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    (n : ℕ) (hX : HasAtlasProperty (@SmoothOfRelativeDimension.{u} n) X)
    {U : Over (Spec (CommRingCat.of k))}
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) (ha : IsEtale a) :
    SmoothOfRelativeDimension n U.hom := by
  obtain ⟨V, b, hb, hbs, hV⟩ := hX
  let hr := X.representable_from_scheme b
  obtain ⟨g, hg⟩ := (schemeYoneda _).map_surjective (hr.fst a)
  have hsq : IsPullback ((schemeYoneda _).map g) ((schemeYoneda _).map (hr.snd a)) b a := by
    rw [hg]
    exact hr.isPullback a
  let : Surjective (hr.snd a).left := hbs.projection a _ _ hsq
  let : Etale (hr.snd a).left := hb.projection a _ _ hsq
  let : Etale g.left := ha.projection b _ _ hsq.flip
  let := hV
  let : SmoothOfRelativeDimension n (hr.pullback a).hom := by
    rw [← Over.w g]
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + n) (g.left ≫ V.hom))
  exact smooth_field_relativeDimension_etale_source_descent k (hr.snd a) n

/-- A rational point has an affine etale source of the same algebraic dimension. -/
structure SmoothPureDimensionalAffineChart (K : Type u) [NontriviallyNormedField K]
    (n : ℕ) (X : AlgebraicSpace (Spec (CommRingCat.of K))) (x : RingPoints K X K) where
  scheme : Over (Spec (CommRingCat.of K))
  isAffine : IsAffine scheme.left
  hom : (schemeToSpace _).obj scheme ⟶ X
  isEtale : IsEtale (AlgebraicSpace.hom hom)
  smooth : SmoothOfRelativeDimension n scheme.hom
  point : RingPoint K scheme K
  map_point : RingPoints.map hom ((schemeRingPointsEquiv K scheme K).symm point) = x

/-- Choose affine etale source charts from the unchanged algebraic smoothness hypothesis. -/
def smoothPureDimensionalAffineChart
    (K : Type u) [NontriviallyNormedField K]
    (n : ℕ) (X : AlgebraicSpace (Spec (CommRingCat.of K)))
    (hX : IsSmoothPureDimensional K n X) (x : RingPoints K X K) :
    SmoothPureDimensionalAffineChart K n X x := by
  apply Classical.choice
  obtain ⟨U, f, hU, hf, u, hu⟩ :=
    RationalPointEtaleLiftProof.rationalPointEtaleLiftStatement K X hX.1.1.1 x
  exact ⟨⟨U, hU, f, hf, smoothRelativeDimension_of_isEtale n hX.2 (hom f) hf, u, hu⟩⟩

namespace SmoothPureDimensionalAffineChart

variable {K : Type u} [NontriviallyNormedField K]
variable {n : ℕ} {X : AlgebraicSpace (Spec (CommRingCat.of K))} {x : RingPoints K X K}

/-- Every chosen source is an actual finite-type etale chart. -/
@[instance_reducible]
def finiteTypeChart (c : SmoothPureDimensionalAffineChart K n X x) : EtaleFiniteTypeChart K X := by
  let := c.isAffine
  let := c.smooth
  let : Smooth c.scheme.hom := SmoothOfRelativeDimension.smooth n c.scheme.hom
  exact ⟨c.scheme, c.hom, c.isEtale, inferInstance, inferInstance⟩

/-- The point map from the source is a local homeomorphism for the existing topologies. -/
theorem isLocalHomeomorph_pointMap [CompleteSpace K]
    (c : SmoothPureDimensionalAffineChart K n X x)
    (hX : IsLocallySeparated X) :
    letI := c.isAffine
    @IsLocalHomeomorph (RingPoint K c.scheme K) (RingPoints K X K) _ (etaleChartTopology K X)
      c.finiteTypeChart.pointMap := by
  let := c.isAffine
  let := c.smooth
  let : Smooth c.scheme.hom := SmoothOfRelativeDimension.smooth n c.scheme.hom
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  have hK := completeHenselianValuedField K
  have hc := c.finiteTypeChart.continuous_pointMap
  have ho := c.finiteTypeChart.isOpenMap_pointMap hK
  change @Continuous (RingPoint K c.scheme K) (RingPoints K X K)
    (schemePointTopology K c.scheme K) _ c.finiteTypeChart.pointMap at hc
  change @IsOpenMap (RingPoint K c.scheme K) (RingPoints K X K)
    (schemePointTopology K c.scheme K) _ c.finiteTypeChart.pointMap at ho
  rw [schemePointTopology_eq_affine] at hc ho
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro u
  obtain ⟨N, hN, huN, hi⟩ :=
    exists_isOpen_injOn_schemePointsMap (AlgebraicSpace.hom c.hom) hX c.isEtale u
  rw [schemePointTopology_eq_affine] at hN
  refine ⟨N, hN.mem_nhds huN, ?_⟩
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap
    (hc.comp continuous_subtype_val) (fun p q h => Subtype.ext (hi p.property q.property h))
    (ho.domRestrict hN)

/-- The source analytic atlas is constructed solely from its algebraic relative dimension. -/
def regularAtlas [CompleteSpace K] (c : SmoothPureDimensionalAffineChart K n X x) :
    letI := c.isAffine
    PointManifold.Analytic.RegularAtlas K c.scheme n := by
  let := c.isAffine
  exact PointManifold.Analytic.smoothAffineRegularAtlas K c.scheme n c.smooth

end SmoothPureDimensionalAffineChart

end Langlands.AlgebraicGeometry.AlgebraicSpace
