import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSpaceAnalyticAtlas
import Langlands.Geometry.Manifold.LocalDiffeomorphDescent

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Set Filter Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped ContDiff Manifold

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K]
variable {n m : ℕ} {X : AlgebraicSpace (Spec (CommRingCat.of K))}
variable {U : Over (Spec (CommRingCat.of K))} [IsAffine U.left]
variable {x : RingPoints K X K}

/-- A common affine neighborhood for an arbitrary affine scheme map and a target etale chart. -/
structure AffineMapRefinement
    (a : (schemeYoneda _).obj U ⟶ X.presheaf)
    (c : SmoothPureDimensionalAffineChart K m X x)
    (n : ℕ) (u : RingPoint K U K) (v : RingPoint K c.scheme K) where
  scheme : Over (Spec (CommRingCat.of K))
  isAffine : IsAffine scheme.left
  smooth : SmoothOfRelativeDimension n scheme.hom
  fst : scheme ⟶ U
  snd : scheme ⟶ c.scheme
  etale_fst : Etale fst.left
  commutes : (schemeYoneda _).map fst ≫ a =
    (schemeYoneda _).map snd ≫ AlgebraicSpace.hom c.hom
  point : RingPoint K scheme K
  fst_point : point ≫ fst = u
  snd_point : point ≫ snd = v

/-- Construct the refinement by an affine open in the represented pullback. -/
def affineMapRefinement
    (a : (schemeYoneda _).obj U ⟶ X.presheaf)
    (c : SmoothPureDimensionalAffineChart K m X x)
    (hU : SmoothOfRelativeDimension n U.hom)
    (u : RingPoint K U K) (v : RingPoint K c.scheme K)
    (huv : schemePointsMap a u = c.finiteTypeChart.pointMap v) :
    AffineMapRefinement a c n u v := by
  apply Classical.choice
  let b : (schemeYoneda _).obj c.scheme ⟶ X.presheaf := AlgebraicSpace.hom c.hom
  obtain ⟨w, hwu, hwv⟩ := exists_pairPullback_point a b huv
  obtain ⟨O, q, hq⟩ := exists_affineOpenPoint K (pairPullback a b) K w
  let T := openOver K (pairPullback a b) O.val
  let i := openOverι K (pairPullback a b) O.val
  let p : T ⟶ U := i ≫ pairPullbackFst a b
  let p' : T ⟶ c.scheme := i ≫ pairPullbackSnd a b
  let : Etale (pairPullbackFst a b).left := etale_pairPullbackFst a b c.isEtale
  let : Etale p.left := by
    change Etale (O.val.ι ≫ (pairPullbackFst a b).left)
    infer_instance
  let := hU
  have hT : SmoothOfRelativeDimension n T.hom := by
    rw [← Over.w p]
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + n) (p.left ≫ U.hom))
  refine ⟨⟨T, O.property, hT, p, p', inferInstance, ?_, q, ?_, ?_⟩⟩
  · change (schemeYoneda _).map (i ≫ pairPullbackFst a b) ≫ a =
      (schemeYoneda _).map (i ≫ pairPullbackSnd a b) ≫ b
    rw [Functor.map_comp_assoc, Functor.map_comp_assoc, (pairPullback_isPullback a b).w]
  · change q ≫ (i ≫ pairPullbackFst a b) = u
    rw [← Category.assoc]
    exact (congrArg (fun z => z ≫ pairPullbackFst a b) hq).trans hwu
  · change q ≫ (i ≫ pairPullbackSnd a b) = v
    rw [← Category.assoc]
    exact (congrArg (fun z => z ≫ pairPullbackSnd a b) hq).trans hwv

omit [IsAffine U.left] in
/-- The refinement commutes on every actual rational point. -/
theorem AffineMapRefinement.pointMap_commutes
    {a : (schemeYoneda _).obj U ⟶ X.presheaf}
    {c : SmoothPureDimensionalAffineChart K m X x}
    {u : RingPoint K U K} {v : RingPoint K c.scheme K}
    (r : AffineMapRefinement a c n u v) (z : RingPoint K r.scheme K) :
    schemePointsMap a (z ≫ r.fst) = c.finiteTypeChart.pointMap (z ≫ r.snd) :=
  congrArg (fun a => a.app (Opposite.op (ringTest K K)) (ULift.up z)) r.commutes

/-- Any algebraic map from a smooth affine scheme lifts analytically through a target
etale point branch. -/
theorem contMDiffAt_affineMap_branch [CompleteSpace K]
    (a : (schemeYoneda _).obj U ⟶ X.presheaf)
    (c : SmoothPureDimensionalAffineChart K m X x)
    (hU : SmoothOfRelativeDimension n U.hom)
    (e : letI := c.isAffine
      @OpenPartialHomeomorph (RingPoint K c.scheme K) (RingPoints K X K) _
        (etaleChartTopology K X))
    (he : EqOn c.finiteTypeChart.pointMap e e.source)
    (u : RingPoint K U K) (hu : schemePointsMap a u ∈ e.target) :
    letI := c.isAffine
    letI := PointManifold.Analytic.smoothAffineChartedSpace K U n hU
    letI := c.regularAtlas.chartedSpace
    letI := etaleChartTopology K X
    ContMDiffAt 𝓘(K, Fin n → K) 𝓘(K, Fin m → K) ω
      (e.symm ∘ schemePointsMap a) u := by
  let := c.isAffine
  let := PointManifold.Analytic.smoothAffineChartedSpace K U n hU
  let := c.regularAtlas.chartedSpace
  let := etaleChartTopology K X
  let v := e.symm (schemePointsMap a u)
  have hv : v ∈ e.source := e.map_target hu
  have huv : schemePointsMap a u = c.finiteTypeChart.pointMap v := by
    rw [he hv, e.right_inv hu]
  let r := affineMapRefinement a c hU u v huv
  let := r.isAffine
  let := r.etale_fst
  let A := PointManifold.Analytic.smoothAffineRegularAtlas K r.scheme n r.smooth
  let B := PointManifold.Analytic.smoothAffineRegularAtlas K U n hU
  let := A.chartedSpace
  have hp := A.isLocalDiffeomorph_postcomp B r.fst
  have hq := A.contMDiff_postcomp c.regularAtlas r.snd
  have hw : r.point ≫ r.snd ∈ e.source := by rw [r.snd_point]; exact hv
  have h := Langlands.Geometry.Manifold.contMDiffAt_branch_lift
    e (schemePointsMap a) c.finiteTypeChart.pointMap he
    (fun z : RingPoint K r.scheme K => z ≫ r.fst)
    (fun z : RingPoint K r.scheme K => z ≫ r.snd)
    r.pointMap_commutes r.point hw (hp r.point) (hq r.point)
  exact r.fst_point ▸ h

/-- Every actual map from a smooth affine scheme to a smooth space is analytic on points. -/
theorem contMDiff_schemePointsMap [CompleteSpace K]
    (hU : SmoothOfRelativeDimension n U.hom)
    (hX : IsSmoothPureDimensional K m X)
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) :
    letI := PointManifold.Analytic.smoothAffineChartedSpace K U n hU
    letI := etaleChartTopology K X
    letI := smoothSpaceChartedSpace K m X hX
    ContMDiff 𝓘(K, Fin n → K) 𝓘(K, Fin m → K) ω (schemePointsMap a) := by
  let := PointManifold.Analytic.smoothAffineChartedSpace K U n hU
  let := etaleChartTopology K X
  let := smoothSpaceChartedSpace K m X hX
  let := hU
  let : Smooth U.hom := SmoothOfRelativeDimension.smooth n U.hom
  have hcont := continuous_schemePointsMap (completeHenselianValuedField K)
    (exists_chart_pointMap_eq hX.1.1.1 hX.1.1.2) a
  rw [schemePointTopology_eq_affine] at hcont
  intro u
  rw [contMDiffAt_iff_target]
  refine ⟨hcont.continuousAt, ?_⟩
  let c := smoothPureDimensionalAffineChart K m X hX (schemePointsMap a u)
  let := c.isAffine
  let := c.regularAtlas.chartedSpace
  let e := c.branch hX.1.2
  have he : EqOn c.finiteTypeChart.pointMap e.symm e.target := by
    intro z _
    exact (congrFun (c.branch_symm hX.1.2) z).symm
  have hbranch := contMDiffAt_affineMap_branch a c hU e.symm he u (c.mem_branch_source hX.1.2)
  have ht := (c.regularAtlas.chartPartialDiffeomorph c.point).contMDiffOn.contMDiffAt
    ((c.regularAtlas.chartAt c.point).homeomorph.open_source.mem_nhds
      (c.regularAtlas.mem_source c.point))
  have ht' : ContMDiffAt 𝓘(K, Fin m → K) 𝓘(K, Fin m → K) ω
      (c.regularAtlas.chartAt c.point).homeomorph (e (schemePointsMap a u)) := by
    rw [c.branch_apply hX.1.2]
    exact ht
  have hfinal := ht'.comp u hbranch
  exact hfinal

end Langlands.AlgebraicGeometry.AlgebraicSpace
