import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothPureDimensionalCharts
import Langlands.AlgebraicGeometry.PointManifold.Analytic.UnramifiedLocalDiffeomorph
import Langlands.Geometry.Manifold.EtaleChartGluing

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Set Filter Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped ContDiff Manifold

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K]
variable {n : ℕ} {X : AlgebraicSpace (Spec (CommRingCat.of K))}
variable {x x' : RingPoints K X K}

namespace SmoothPureDimensionalAffineChart

/-- A common affine etale neighborhood of two chart points with the same image. -/
structure Refinement
    (c : SmoothPureDimensionalAffineChart K n X x)
    (c' : SmoothPureDimensionalAffineChart K n X x')
    (u : RingPoint K c.scheme K) (v : RingPoint K c'.scheme K) where
  scheme : Over (Spec (CommRingCat.of K))
  isAffine : IsAffine scheme.left
  smooth : SmoothOfRelativeDimension n scheme.hom
  fst : scheme ⟶ c.scheme
  snd : scheme ⟶ c'.scheme
  etale_fst : Etale fst.left
  etale_snd : Etale snd.left
  commutes : (schemeYoneda _).map fst ≫ AlgebraicSpace.hom c.hom =
    (schemeYoneda _).map snd ≫ AlgebraicSpace.hom c'.hom
  point : RingPoint K scheme K
  fst_point : point ≫ fst = u
  snd_point : point ≫ snd = v

/-- Choose a common affine etale refinement using the represented fibre product. -/
def refinement
    (c : SmoothPureDimensionalAffineChart K n X x)
    (c' : SmoothPureDimensionalAffineChart K n X x')
    (u : RingPoint K c.scheme K) (v : RingPoint K c'.scheme K)
    (huv : c.finiteTypeChart.pointMap u = c'.finiteTypeChart.pointMap v) :
    Refinement c c' u v := by
  apply Classical.choice
  let a : (schemeYoneda _).obj c.scheme ⟶ X.presheaf := AlgebraicSpace.hom c.hom
  let b : (schemeYoneda _).obj c'.scheme ⟶ X.presheaf := AlgebraicSpace.hom c'.hom
  obtain ⟨w, hwu, hwv⟩ := exists_pairPullback_point a b huv
  obtain ⟨O, q, hq⟩ := exists_affineOpenPoint K (pairPullback a b) K w
  let T := openOver K (pairPullback a b) O.val
  let i := openOverι K (pairPullback a b) O.val
  let p : T ⟶ c.scheme := i ≫ pairPullbackFst a b
  let p' : T ⟶ c'.scheme := i ≫ pairPullbackSnd a b
  let : Etale (pairPullbackFst a b).left := etale_pairPullbackFst a b c'.isEtale
  let : Etale (pairPullbackSnd a b).left := etale_pairPullbackSnd a b c.isEtale
  let : Etale p.left := by
    change Etale (O.val.ι ≫ (pairPullbackFst a b).left)
    infer_instance
  let : Etale p'.left := by
    change Etale (O.val.ι ≫ (pairPullbackSnd a b).left)
    infer_instance
  let := c.smooth
  have hT : SmoothOfRelativeDimension n T.hom := by
    rw [← Over.w p]
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + n) (p.left ≫ c.scheme.hom))
  refine ⟨⟨T, O.property, hT, p, p', inferInstance, inferInstance, ?_, q, ?_, ?_⟩⟩
  · change (schemeYoneda _).map (i ≫ pairPullbackFst a b) ≫ a =
      (schemeYoneda _).map (i ≫ pairPullbackSnd a b) ≫ b
    rw [Functor.map_comp_assoc, Functor.map_comp_assoc, (pairPullback_isPullback a b).w]
  · change q ≫ (i ≫ pairPullbackFst a b) = u
    rw [← Category.assoc]
    exact (congrArg (fun z => z ≫ pairPullbackFst a b) hq).trans hwu
  · change q ≫ (i ≫ pairPullbackSnd a b) = v
    rw [← Category.assoc]
    exact (congrArg (fun z => z ≫ pairPullbackSnd a b) hq).trans hwv

namespace Refinement

variable {c : SmoothPureDimensionalAffineChart K n X x}
variable {c' : SmoothPureDimensionalAffineChart K n X x'}
variable {u : RingPoint K c.scheme K} {v : RingPoint K c'.scheme K}

/-- The refinement commutes on every actual rational point. -/
theorem pointMap_commutes (r : Refinement c c' u v) (z : RingPoint K r.scheme K) :
    c.finiteTypeChart.pointMap (z ≫ r.fst) =
      c'.finiteTypeChart.pointMap (z ≫ r.snd) :=
  congrArg (fun a => a.app (Opposite.op (ringTest K K)) (ULift.up z)) r.commutes

end Refinement

/-- Changes between topological branches of affine etale charts are analytic. -/
theorem contMDiffAt_branch_transition [CompleteSpace K]
    (c : SmoothPureDimensionalAffineChart K n X x)
    (c' : SmoothPureDimensionalAffineChart K n X x')
    (e : letI := c.isAffine
      @OpenPartialHomeomorph (RingPoint K c.scheme K) (RingPoints K X K) _
        (etaleChartTopology K X))
    (e' : letI := c'.isAffine
      @OpenPartialHomeomorph (RingPoint K c'.scheme K) (RingPoints K X K) _
        (etaleChartTopology K X))
    (he : EqOn c.finiteTypeChart.pointMap e e.source)
    (he' : EqOn c'.finiteTypeChart.pointMap e' e'.source)
    (u : RingPoint K c.scheme K) (hu : u ∈ e.source) (hu' : e u ∈ e'.target) :
    letI := c.isAffine
    letI := c'.isAffine
    letI := c.regularAtlas.chartedSpace
    letI := c'.regularAtlas.chartedSpace
    letI := etaleChartTopology K X
    ContMDiffAt 𝓘(K, Fin n → K) 𝓘(K, Fin n → K) ω (e'.symm ∘ e) u := by
  let := c.isAffine
  let := c'.isAffine
  let := c.regularAtlas.chartedSpace
  let := c'.regularAtlas.chartedSpace
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let v := e'.symm (e u)
  have hv : v ∈ e'.source := e'.map_target hu'
  have huv : c.finiteTypeChart.pointMap u = c'.finiteTypeChart.pointMap v := by
    rw [he hu, he' hv, e'.right_inv hu']
  let r := c.refinement c' u v huv
  let := r.isAffine
  let := r.etale_fst
  let := r.etale_snd
  let A := PointManifold.Analytic.smoothAffineRegularAtlas K r.scheme n r.smooth
  let := A.chartedSpace
  have hp := A.isLocalDiffeomorph_postcomp c.regularAtlas r.fst
  have hq := A.isLocalDiffeomorph_postcomp c'.regularAtlas r.snd
  have hw : r.point ≫ r.fst ∈ e.source := by rw [r.fst_point]; exact hu
  have hw' : r.point ≫ r.snd ∈ e'.source := by rw [r.snd_point]; exact hv
  have h := Langlands.Geometry.Manifold.contMDiffAt_branch_transition
    e e' c.finiteTypeChart.pointMap c'.finiteTypeChart.pointMap he he'
    (fun z : RingPoint K r.scheme K => z ≫ r.fst)
    (fun z : RingPoint K r.scheme K => z ≫ r.snd)
    r.pointMap_commutes r.point hw hw' (hp r.point) (hq r.point).contMDiffAt
  exact r.fst_point ▸ h

end SmoothPureDimensionalAffineChart

end Langlands.AlgebraicGeometry.AlgebraicSpace
