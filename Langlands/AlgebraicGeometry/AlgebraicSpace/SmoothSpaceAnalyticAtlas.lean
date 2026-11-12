import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothChartRefinement

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Set Filter Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped ContDiff Manifold

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
variable {n : ℕ} {X : AlgebraicSpace (Spec (CommRingCat.of K))}
variable {x x' : RingPoints K X K}

namespace SmoothPureDimensionalAffineChart

/-- A topological inverse branch of the affine chart point map at its lifted point. -/
@[instance_reducible]
def branch (c : SmoothPureDimensionalAffineChart K n X x) (hX : IsLocallySeparated X) :
    letI := c.isAffine
    @OpenPartialHomeomorph (RingPoints K X K) (RingPoint K c.scheme K)
      (etaleChartTopology K X) _ := by
  let := c.isAffine
  let := etaleChartTopology K X
  exact (c.isLocalHomeomorph_pointMap hX).localInverseAt c.point

/-- The reverse branch is the actual chart map, on its entire underlying function. -/
theorem branch_symm (c : SmoothPureDimensionalAffineChart K n X x)
    (hX : IsLocallySeparated X) :
    letI := c.isAffine
    letI := etaleChartTopology K X
    (c.branch hX).symm = c.finiteTypeChart.pointMap := by
  let := c.isAffine
  let := etaleChartTopology K X
  exact (c.isLocalHomeomorph_pointMap hX).localInverseAt_symm c.point

/-- The chosen inverse branch contains the specified space point. -/
theorem mem_branch_source (c : SmoothPureDimensionalAffineChart K n X x)
    (hX : IsLocallySeparated X) :
    letI := c.isAffine
    x ∈ (c.branch hX).source := by
  let := c.isAffine
  let := etaleChartTopology K X
  have h : c.finiteTypeChart.pointMap c.point ∈ (c.branch hX).source :=
    (c.isLocalHomeomorph_pointMap hX).apply_self_mem_localInverseAt_source
  exact (congrArg (fun z => z ∈ (c.branch hX).source) c.map_point).mp h

/-- The inverse branch sends the specified point to its chosen rational lift. -/
theorem branch_apply (c : SmoothPureDimensionalAffineChart K n X x)
    (hX : IsLocallySeparated X) :
    letI := c.isAffine
    (c.branch hX) x = c.point := by
  let := c.isAffine
  let := etaleChartTopology K X
  have h : c.branch hX (c.finiteTypeChart.pointMap c.point) = c.point :=
    (c.isLocalHomeomorph_pointMap hX).localInverseAt_apply_self
  exact (congrArg (c.branch hX) c.map_point).symm.trans h

/-- A model chart on space points, transported from the regular analytic source chart. -/
@[instance_reducible]
def modelChart (c : SmoothPureDimensionalAffineChart K n X x) (hX : IsLocallySeparated X) :
    @OpenPartialHomeomorph (RingPoints K X K) (Fin n → K) (etaleChartTopology K X) _ := by
  let := c.isAffine
  let := etaleChartTopology K X
  exact (c.branch hX).trans (c.regularAtlas.chartAt c.point).homeomorph

/-- The transported chart contains the specified space point. -/
theorem mem_modelChart_source (c : SmoothPureDimensionalAffineChart K n X x)
    (hX : IsLocallySeparated X) : x ∈ (c.modelChart hX).source := by
  let := c.isAffine
  let := etaleChartTopology K X
  refine ⟨c.mem_branch_source hX, ?_⟩
  change c.branch hX x ∈ (c.regularAtlas.chartAt c.point).homeomorph.source
  rw [c.branch_apply hX]
  exact c.regularAtlas.mem_source c.point

/-- Any two transported model charts have analytic transition maps on their full overlap. -/
theorem contDiffOn_modelChart_transition
    (c : SmoothPureDimensionalAffineChart K n X x)
    (c' : SmoothPureDimensionalAffineChart K n X x')
    (hX : IsLocallySeparated X) :
    letI := etaleChartTopology K X
    ContDiffOn K ω ((c.modelChart hX).symm.trans (c'.modelChart hX))
      ((c.modelChart hX).symm.trans (c'.modelChart hX)).source := by
  let := c.isAffine
  let := c'.isAffine
  let := c.regularAtlas.chartedSpace
  let := c'.regularAtlas.chartedSpace
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let e := c.branch hX
  let e' := c'.branch hX
  let s := c.regularAtlas.chartAt c.point
  let t := c'.regularAtlas.chartAt c'.point
  apply contMDiffOn_iff_contDiffOn.mp
  intro y hy
  have hyT : y ∈ s.homeomorph.target := hy.1.1
  have hyE : s.homeomorph.symm y ∈ e.target := hy.1.2
  have hyE' : e.symm (s.homeomorph.symm y) ∈ e'.source := hy.2.1
  have hyS : e' (e.symm (s.homeomorph.symm y)) ∈ t.homeomorph.source := hy.2.2
  have he : EqOn c.finiteTypeChart.pointMap e.symm e.target := by
    intro z _
    exact (congrFun (c.branch_symm hX) z).symm
  have he' : EqOn c'.finiteTypeChart.pointMap e'.symm e'.target := by
    intro z _
    exact (congrFun (c'.branch_symm hX) z).symm
  have hmid := c.contMDiffAt_branch_transition c' e.symm e'.symm he he'
    (s.homeomorph.symm y) hyE hyE'
  have hs := (c.regularAtlas.chartPartialDiffeomorph c.point).symm.contMDiffOn.contMDiffAt
    (s.homeomorph.open_target.mem_nhds hyT)
  have ht := (c'.regularAtlas.chartPartialDiffeomorph c'.point).contMDiffOn.contMDiffAt
    (t.homeomorph.open_source.mem_nhds hyS)
  exact (ht.comp y (hmid.comp y hs)).contMDiffWithinAt

end SmoothPureDimensionalAffineChart

/-- The charted space on actual rational points, with the published etale-chart topology. -/
@[instance_reducible]
def smoothSpaceChartedSpace (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (n : ℕ) (X : AlgebraicSpace (Spec (CommRingCat.of K)))
    (hX : IsSmoothPureDimensional K n X) :
    @ChartedSpace (Fin n → K) _ (RingPoints K X K) (etaleChartTopology K X) := by
  let := etaleChartTopology K X
  exact {
    atlas := Set.range fun x => (smoothPureDimensionalAffineChart K n X hX x).modelChart hX.1.2
    chartAt x := (smoothPureDimensionalAffineChart K n X hX x).modelChart hX.1.2
    mem_chart_source x := (smoothPureDimensionalAffineChart K n X hX x).mem_modelChart_source hX.1.2
    chart_mem_atlas x := ⟨x, rfl⟩ }

/-- The transported atlas is an analytic manifold over the original field. -/
theorem smoothSpaceIsManifold (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (n : ℕ) (X : AlgebraicSpace (Spec (CommRingCat.of K)))
    (hX : IsSmoothPureDimensional K n X) :
    letI := etaleChartTopology K X
    letI := smoothSpaceChartedSpace K n X hX
    IsManifold 𝓘(K, Fin n → K) ω (RingPoints K X K) := by
  let := etaleChartTopology K X
  let := smoothSpaceChartedSpace K n X hX
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' => ?_
  obtain ⟨x, rfl⟩ := he
  obtain ⟨x', rfl⟩ := he'
  rw [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, inter_univ,
    preimage_id, Function.id_comp, Function.comp_id]
  exact (smoothPureDimensionalAffineChart K n X hX x).contDiffOn_modelChart_transition
    (smoothPureDimensionalAffineChart K n X hX x') hX.1.2

/-- The family of analytic charted spaces constructed from the algebraic hypotheses alone. -/
def canonicalAnalyticPointStructure (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] :
    AnalyticPointStructure K :=
  ⟨smoothSpaceChartedSpace K⟩

/-- The canonical family consists of analytic manifolds. -/
theorem canonicalAnalyticPointStructure_isAnalytic (K : Type u) [NontriviallyNormedField K]
    [CompleteSpace K] : (canonicalAnalyticPointStructure K).IsAnalytic :=
  smoothSpaceIsManifold K

end Langlands.AlgebraicGeometry.AlgebraicSpace
