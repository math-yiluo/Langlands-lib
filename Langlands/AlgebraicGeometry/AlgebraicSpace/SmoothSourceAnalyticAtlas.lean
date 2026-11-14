import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionFieldPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyFunctorial

/-! # Charts of varying dimension on actual smooth-space rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped ContDiff Manifold

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- Topological charts on the original point space, with the intrinsic dimension
allowed to vary between their open sources. This is chart data and its intrinsic
laws; analyticity is a separate predicate. -/
structure DimensionPointAtlas (hX : SmoothOverBase X) where
  atlas : ∀ n : ℕ, Set (@OpenPartialHomeomorph (RingPoints K X K) (Fin n → K)
    (etaleChartTopology K X) inferInstance)
  chartAt : ∀ x : RingPoints K X K,
    @OpenPartialHomeomorph (RingPoints K X K)
      (Fin (SmoothDimensionPieces.fieldPointDimension hX x) → K)
      (etaleChartTopology K X) inferInstance
  mem_chart_source : ∀ x, x ∈ (chartAt x).source
  chart_mem_atlas : ∀ x, chartAt x ∈ atlas (SmoothDimensionPieces.fieldPointDimension hX x)
  source_dimension : ∀ n e, e ∈ atlas n → ∀ x ∈ e.source,
    SmoothDimensionPieces.fieldPointDimension hX x = n

namespace DimensionPointAtlas

variable {hX : SmoothOverBase X} (A : DimensionPointAtlas hX)

/-- Charts in different dimensions have disjoint sources in the actual point space. -/
theorem disjoint_sources {n m : ℕ}
    {e : @OpenPartialHomeomorph (RingPoints K X K) (Fin n → K)
      (etaleChartTopology K X) inferInstance}
    {e' : @OpenPartialHomeomorph (RingPoints K X K) (Fin m → K)
      (etaleChartTopology K X) inferInstance}
    (he : e ∈ A.atlas n) (he' : e' ∈ A.atlas m) (hnm : n ≠ m) :
    Disjoint e.source e'.source := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  exact hnm ((A.source_dimension n e he x hx).symm.trans
    (A.source_dimension m e' he' x hx'))

/-- Every point of the original point space lies in a chart of its actual dimension. -/
theorem covers (x : RingPoints K X K) :
    ∃ e ∈ A.atlas (SmoothDimensionPieces.fieldPointDimension hX x), x ∈ e.source :=
  ⟨A.chartAt x, A.chart_mem_atlas x, A.mem_chart_source x⟩

/-- Analytic transition functions on every nonempty possible overlap. Charts of
different dimensions already have disjoint sources. -/
def IsAnalytic : Prop :=
  letI := etaleChartTopology K X
  ∀ n, ∀ e ∈ A.atlas n, ∀ e' ∈ A.atlas n,
    ContDiffOn K ω (e.symm.trans e') (e.symm.trans e').source

variable {Y : AlgebraicSpace (Spec (CommRingCat.of K))}
  {hY : SmoothOverBase Y} (B : DimensionPointAtlas hY)

/-- Analyticity on a subset includes continuity for the original topologies and
is tested in every pair of source and target charts. The coordinate domain
retains the intersection with the target chart, including target pieces whose
dimension differs from the source piece. -/
def AnalyticOn (f : RingPoints K X K → RingPoints K Y K)
    (s : Set (RingPoints K X K)) : Prop :=
  letI := etaleChartTopology K X
  letI := etaleChartTopology K Y
  ContinuousOn f s ∧
  ∀ n m, ∀ e ∈ A.atlas n, ∀ e' ∈ B.atlas m,
    ContDiffOn K ω (e' ∘ f ∘ e.symm)
      (e.target ∩ e.symm ⁻¹' (s ∩ f ⁻¹' e'.source))

/-- An analytic map on the whole original rational-point space. -/
def AnalyticMap (f : RingPoints K X K → RingPoints K Y K) : Prop :=
  A.AnalyticOn B f Set.univ

/-- Local analytic isomorphisms on actual points, including preservation of the
intrinsic dimension and analytic inverse branches for the original topologies. -/
def IsLocalAnalyticIso (f : RingPoints K X K → RingPoints K Y K) : Prop :=
  letI := etaleChartTopology K X
  letI := etaleChartTopology K Y
  (∀ x, SmoothDimensionPieces.fieldPointDimension hY (f x) =
    SmoothDimensionPieces.fieldPointDimension hX x) ∧
  ∀ x, ∃ e : @OpenPartialHomeomorph (RingPoints K X K) (RingPoints K Y K)
      (etaleChartTopology K X) (etaleChartTopology K Y),
    x ∈ e.source ∧ Set.EqOn e f e.source ∧
      A.AnalyticOn B e e.source ∧ B.AnalyticOn A e.symm e.target

/-- Equality of the analytic structures means that the actual identity map is
analytic in both directions, rather than equality of chosen charts. -/
def Equivalent (B : DimensionPointAtlas hX) : Prop :=
  A.AnalyticMap B id ∧ B.AnalyticMap A id

end DimensionPointAtlas

namespace AnalyticPointStructure

variable (σ : AnalyticPointStructure K)
  (hK : IsHenselianValuedField K) (hX : SmoothOverBase X)
  (hqs : IsQuasiSeparated X) (hls : IsLocallySeparated X)

include hK hqs in
/-- The actual inclusion of each algebraic dimension piece is an open embedding
on rational points for the independently defined chart topologies. -/
theorem dimensionPiece_isOpenEmbedding (n : ℕ) :
    @IsOpenEmbedding _ _
      (etaleChartTopology K (SmoothDimensionPieces.space hX n))
      (etaleChartTopology K X)
      (RingPoints.map (A := K) (SmoothDimensionPieces.inclusion hX n)) :=
  isOpenEmbedding_ringPointsMap hK
    ⟨SmoothDimensionPieces.space_isQuasiSeparated hX hqs n,
      (SmoothDimensionPieces.space_smoothOverBase hX n).locallyOfFiniteType⟩
    ⟨hqs, hX.locallyOfFiniteType⟩
    (SmoothDimensionPieces.inclusion hX n)
    (SmoothDimensionPieces.inclusion_isOpenImmersion hX n)

/-- Lift one pure-dimensional chart along the actual inclusion of its piece.
The resulting chart has an open source in the original point space. -/
def liftDimensionChart (n : ℕ)
    (e : @OpenPartialHomeomorph
      (RingPoints K (SmoothDimensionPieces.space hX n) K) (Fin n → K)
      (etaleChartTopology K (SmoothDimensionPieces.space hX n)) inferInstance) :
    @OpenPartialHomeomorph (RingPoints K X K) (Fin n → K)
      (etaleChartTopology K X) inferInstance := by
  letI := etaleChartTopology K X
  letI := etaleChartTopology K (SmoothDimensionPieces.space hX n)
  exact e.lift_openEmbedding (dimensionPiece_isOpenEmbedding hK hX hqs n)

/-- All charts from a piece's supplied charted space, lifted into actual `X(K)`. -/
def dimensionAtlasCharts (n : ℕ) :
    Set (@OpenPartialHomeomorph (RingPoints K X K) (Fin n → K)
      (etaleChartTopology K X) inferInstance) := by
  letI := etaleChartTopology K (SmoothDimensionPieces.space hX n)
  letI := σ.chartedSpace n (SmoothDimensionPieces.space hX n)
    (SmoothDimensionPieces.space_isSmoothPureDimensional hX hqs hls n)
  exact liftDimensionChart hK hX hqs n '' atlas (Fin n → K)
    (RingPoints K (SmoothDimensionPieces.space hX n) K)

/-- The chosen chart at the actual factorization of a point, lifted to `X(K)`. -/
def dimensionChartAt (x : RingPoints K X K) :
    @OpenPartialHomeomorph (RingPoints K X K)
      (Fin (SmoothDimensionPieces.fieldPointDimension hX x) → K)
      (etaleChartTopology K X) inferInstance := by
  let n := SmoothDimensionPieces.fieldPointDimension hX x
  letI := etaleChartTopology K (SmoothDimensionPieces.space hX n)
  letI := σ.chartedSpace n (SmoothDimensionPieces.space hX n)
    (SmoothDimensionPieces.space_isSmoothPureDimensional hX hqs hls n)
  exact liftDimensionChart hK hX hqs n
    (chartAt (Fin n → K) (SmoothDimensionPieces.fieldPointFactor hX x))

/-- A concrete varying-dimension topological atlas on the original rational
points, computed from the pure-dimensional family and actual open pieces. -/
def dimensionAtlas : DimensionPointAtlas hX where
  atlas := σ.dimensionAtlasCharts hK hX hqs hls
  chartAt := σ.dimensionChartAt hK hX hqs hls
  mem_chart_source x := by
    let n := SmoothDimensionPieces.fieldPointDimension hX x
    let := etaleChartTopology K (SmoothDimensionPieces.space hX n)
    let := σ.chartedSpace n (SmoothDimensionPieces.space hX n)
      (SmoothDimensionPieces.space_isSmoothPureDimensional hX hqs hls n)
    exact ⟨SmoothDimensionPieces.fieldPointFactor hX x, mem_chart_source (Fin n → K) _,
      SmoothDimensionPieces.fieldPointFactor_map hX x⟩
  chart_mem_atlas x := by
    let n := SmoothDimensionPieces.fieldPointDimension hX x
    let := etaleChartTopology K (SmoothDimensionPieces.space hX n)
    let := σ.chartedSpace n (SmoothDimensionPieces.space hX n)
      (SmoothDimensionPieces.space_isSmoothPureDimensional hX hqs hls n)
    exact ⟨chartAt (Fin n → K) (SmoothDimensionPieces.fieldPointFactor hX x),
      chart_mem_atlas (Fin n → K) _, rfl⟩
  source_dimension n e he x hx := by
    obtain ⟨c, _, rfl⟩ := he
    obtain ⟨y, _, rfl⟩ := hx
    exact SmoothDimensionPieces.fieldPointDimension_map_inclusion hX n y

/-- Lifting changes no coordinate transition within a dimension piece. -/
theorem liftDimensionChart_transition (n : ℕ)
    (e e' : @OpenPartialHomeomorph
      (RingPoints K (SmoothDimensionPieces.space hX n) K) (Fin n → K)
      (etaleChartTopology K (SmoothDimensionPieces.space hX n)) inferInstance) :
    letI := etaleChartTopology K X
    letI := etaleChartTopology K (SmoothDimensionPieces.space hX n)
    (liftDimensionChart hK hX hqs n e).symm.trans
      (liftDimensionChart hK hX hqs n e') = e.symm.trans e' := by
  let := etaleChartTopology K X
  let := etaleChartTopology K (SmoothDimensionPieces.space hX n)
  exact OpenPartialHomeomorph.lift_openEmbedding_trans e e'
    (dimensionPiece_isOpenEmbedding hK hX hqs n)

end AnalyticPointStructure

end Langlands.AlgebraicGeometry.AlgebraicSpace
