import Langlands.AlgebraicGeometry.AlgebraicSpace.AnalyticSchemePointMaps

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Set Filter Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped ContDiff Manifold

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
variable {n m : ℕ} {X Y : AlgebraicSpace (Spec (CommRingCat.of K))}
variable {x : RingPoints K X K}

namespace SmoothPureDimensionalAffineChart

/-- Every inverse branch of an affine chart is analytic into its regular source manifold. -/
theorem contMDiffOn_branch
    (c : SmoothPureDimensionalAffineChart K n X x)
    (hX : IsSmoothPureDimensional K n X) :
    letI := c.isAffine
    letI := etaleChartTopology K X
    letI := smoothSpaceChartedSpace K n X hX
    letI := c.regularAtlas.chartedSpace
    ContMDiffOn 𝓘(K, Fin n → K) 𝓘(K, Fin n → K) ω
      (c.branch hX.1.2) (c.branch hX.1.2).source := by
  let := c.isAffine
  let := etaleChartTopology K X
  let := smoothSpaceChartedSpace K n X hX
  let := c.regularAtlas.chartedSpace
  intro z hz
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source]
  let d := smoothPureDimensionalAffineChart K n X hX z
  let := d.isAffine
  let := d.regularAtlas.chartedSpace
  let e := c.branch hX.1.2
  let e' := d.branch hX.1.2
  let s := d.regularAtlas.chartAt d.point
  have he : EqOn c.finiteTypeChart.pointMap e.symm e.target := by
    intro u _
    exact (congrFun (c.branch_symm hX.1.2) u).symm
  have he' : EqOn d.finiteTypeChart.pointMap e'.symm e'.target := by
    intro u _
    exact (congrFun (d.branch_symm hX.1.2) u).symm
  have hdz : e' z = d.point := d.branch_apply hX.1.2
  have hmem : e' z ∈ e'.target := e'.map_source (d.mem_branch_source hX.1.2)
  have hz' : e'.symm (e' z) ∈ e.source := by
    rw [e'.left_inv (d.mem_branch_source hX.1.2)]
    exact hz
  have hmid := d.contMDiffAt_branch_transition c e'.symm e.symm he' he
    (e' z) hmem hz'
  have hs0 : e' z ∈ s.homeomorph.source := by
    rw [hdz]
    exact d.regularAtlas.mem_source d.point
  have hy : s.homeomorph (e' z) ∈ s.homeomorph.target := s.homeomorph.map_source hs0
  have hs := (d.regularAtlas.chartPartialDiffeomorph d.point).symm.contMDiffOn.contMDiffAt
    (s.homeomorph.open_target.mem_nhds hy)
  have hmid' : ContMDiffAt 𝓘(K, Fin n → K) 𝓘(K, Fin n → K) ω
      (e ∘ e'.symm) (s.homeomorph.symm (s.homeomorph (e' z))) := by
    rw [s.homeomorph.left_inv hs0]
    exact hmid
  have hfinal := (hmid'.comp (s.homeomorph (e' z)) hs).contMDiffWithinAt (s := univ)
  rw [modelWithCornersSelf_coe, range_id]
  change ContMDiffWithinAt 𝓘(K, Fin n → K) 𝓘(K, Fin n → K) ω
    (e ∘ e'.symm ∘ s.homeomorph.symm) univ (s.homeomorph (e' z))
  exact hfinal

/-- The topological inverse branch is a partial analytic diffeomorphism. -/
@[instance_reducible]
def branchPartialDiffeomorph
    (c : SmoothPureDimensionalAffineChart K n X x)
    (hX : IsSmoothPureDimensional K n X) :
    letI := c.isAffine
    letI := etaleChartTopology K X
    letI := smoothSpaceChartedSpace K n X hX
    letI := c.regularAtlas.chartedSpace
    PartialDiffeomorph 𝓘(K, Fin n → K) 𝓘(K, Fin n → K)
      (RingPoints K X K) (RingPoint K c.scheme K) ω := by
  let := c.isAffine
  let := etaleChartTopology K X
  let := smoothSpaceChartedSpace K n X hX
  let := c.regularAtlas.chartedSpace
  refine {
    toPartialEquiv := (c.branch hX.1.2).toPartialEquiv
    open_source := (c.branch hX.1.2).open_source
    open_target := (c.branch hX.1.2).open_target
    contMDiffOn_toFun := c.contMDiffOn_branch hX
    contMDiffOn_invFun := ?_ }
  have hf := contMDiff_schemePointsMap c.smooth hX (AlgebraicSpace.hom c.hom)
  change ContMDiffOn 𝓘(K, Fin n → K) 𝓘(K, Fin n → K) ω
    (c.branch hX.1.2).symm (c.branch hX.1.2).target
  exact hf.contMDiffOn.congr fun u _ => congrFun (c.branch_symm hX.1.2) u

/-- The actual affine chart point map is a local analytic diffeomorphism at the lift. -/
theorem isLocalDiffeomorphAt_pointMap
    (c : SmoothPureDimensionalAffineChart K n X x)
    (hX : IsSmoothPureDimensional K n X) :
    letI := c.isAffine
    letI := etaleChartTopology K X
    letI := smoothSpaceChartedSpace K n X hX
    letI := c.regularAtlas.chartedSpace
    IsLocalDiffeomorphAt 𝓘(K, Fin n → K) 𝓘(K, Fin n → K) ω
      c.finiteTypeChart.pointMap c.point := by
  let := c.isAffine
  let := etaleChartTopology K X
  let := smoothSpaceChartedSpace K n X hX
  let := c.regularAtlas.chartedSpace
  refine ⟨(c.branchPartialDiffeomorph hX).symm, ?_, ?_⟩
  · change c.point ∈ (c.branch hX.1.2).target
    exact (c.isLocalHomeomorph_pointMap hX.1.2).self_mem_localInverseAt_target
  · intro u _
    change c.finiteTypeChart.pointMap u = (c.branch hX.1.2).symm u
    exact (congrFun (c.branch_symm hX.1.2) u).symm

end SmoothPureDimensionalAffineChart

/-- Actual algebraic-space morphisms induce analytic maps on the constructed manifolds. -/
theorem contMDiff_ringPointsMap
    (hX : IsSmoothPureDimensional K n X) (hY : IsSmoothPureDimensional K m Y) (f : X ⟶ Y) :
    letI := etaleChartTopology K X
    letI := etaleChartTopology K Y
    letI := smoothSpaceChartedSpace K n X hX
    letI := smoothSpaceChartedSpace K m Y hY
    ContMDiff 𝓘(K, Fin n → K) 𝓘(K, Fin m → K) ω (RingPoints.map (A := K) f) := by
  let := etaleChartTopology K X
  let := etaleChartTopology K Y
  let := smoothSpaceChartedSpace K n X hX
  let := smoothSpaceChartedSpace K m Y hY
  intro z
  let c := smoothPureDimensionalAffineChart K n X hX z
  let := c.isAffine
  let := c.regularAtlas.chartedSpace
  have hp := c.isLocalDiffeomorphAt_pointMap hX
  have hc := contMDiff_schemePointsMap c.smooth hY (AlgebraicSpace.hom c.hom ≫ hom f)
  have h := Langlands.Geometry.Manifold.contMDiffAt_of_comp_localDiffeomorph
    c.finiteTypeChart.pointMap (RingPoints.map (A := K) f) c.point hp (hc c.point)
  exact c.map_point ▸ h

/-- The canonical family has analytic functoriality. -/
theorem canonicalAnalyticPointStructure_isFunctorial (K : Type u)
    [NontriviallyNormedField K] [CompleteSpace K] :
    (canonicalAnalyticPointStructure K).IsFunctorial :=
  fun _ _ _ _ hX hY f => contMDiff_ringPointsMap hX hY f

/-- Etale space morphisms induce local analytic isomorphisms. -/
theorem isLocalDiffeomorph_ringPointsMap
    (hX : IsSmoothPureDimensional K n X) (hY : IsSmoothPureDimensional K n Y)
    (f : X ⟶ Y) (hf : IsEtaleMorphism f) :
    letI := etaleChartTopology K X
    letI := etaleChartTopology K Y
    letI := smoothSpaceChartedSpace K n X hX
    letI := smoothSpaceChartedSpace K n Y hY
    IsLocalDiffeomorph 𝓘(K, Fin n → K) 𝓘(K, Fin n → K) ω
      (RingPoints.map (A := K) f) := by
  let := etaleChartTopology K X
  let := etaleChartTopology K Y
  let := smoothSpaceChartedSpace K n X hX
  let := smoothSpaceChartedSpace K n Y hY
  intro z
  let c := smoothPureDimensionalAffineChart K n X hX z
  let := c.isAffine
  let := c.regularAtlas.chartedSpace
  let d : SmoothPureDimensionalAffineChart K n Y (RingPoints.map (A := K) f z) := {
    scheme := c.scheme
    isAffine := c.isAffine
    hom := c.hom ≫ f
    isEtale := hf _ _ c.isEtale
    smooth := c.smooth
    point := c.point
    map_point := congrArg (RingPoints.map (A := K) f) c.map_point }
  have hp := c.isLocalDiffeomorphAt_pointMap hX
  have hcomp := d.isLocalDiffeomorphAt_pointMap hY
  have h := Langlands.Geometry.Manifold.isLocalDiffeomorphAt_of_comp
    c.finiteTypeChart.pointMap (RingPoints.map (A := K) f) c.point hp hcomp
  exact c.map_point ▸ h

/-- The canonical family sends etale morphisms to analytic local isomorphisms. -/
theorem canonicalAnalyticPointStructure_isEtaleLocalIso (K : Type u)
    [NontriviallyNormedField K] [CompleteSpace K] :
    (canonicalAnalyticPointStructure K).IsEtaleLocalIso :=
  fun _ _ _ hX hY f hf => isLocalDiffeomorph_ringPointsMap hX hY f hf

end Langlands.AlgebraicGeometry.AlgebraicSpace
