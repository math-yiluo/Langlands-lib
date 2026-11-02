import Langlands.GroupScheme.AffinePointRingPointComparison
import Langlands.GroupScheme.AffinePointCoordinateSmooth
import Langlands.AlgebraicGeometry.PointManifold.RegularEvaluation

/-! # The regular-function family criterion on actual affine group points -/

noncomputable section

universe v w

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped Manifold ContDiff CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.AlgebraicGeometry.PointManifold

set_option backward.isDefEq.respectTransparency false

variable {k : Type} [RCLike k]
variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

local instance : TopologicalSpace (G.affinePoints (CommAlgCat.of k k)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of k k)

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- The two criteria test the same actual global-function values. -/
theorem regularSmooth_iff_coordinateSmooth
    (p : M → G.affinePoints (CommAlgCat.of k k)) :
    RegularSmooth I
        (fun t => G.affinePointsRingPointHomeomorph (CommAlgCat.of k k) (p t)) ↔
      G.CoordinateSmooth (CommAlgCat.of k k) (RingHom.id k) I p := by
  apply forall_congr'
  intro a
  have h (t : M) :
      regularEvaluation
          (G.affinePointsRingPointHomeomorph (CommAlgCat.of k k) (p t)) a =
        G.affinePointEvaluation (CommAlgCat.of k k) (p t) a :=
    G.affinePointsRingPointHomeomorph_evaluation (CommAlgCat.of k k) (p t) a
  change ContMDiff I 𝓘(ℝ, k) ∞ _ ↔ ContMDiff I 𝓘(ℝ, k) ∞ _
  simp_rw [h]
  rfl

/-- Transport coordinate-smooth families to regular-smooth families along the
identity homeomorphism of the actual point carriers. -/
def coordinateSmoothRegularSmoothFamilyEquiv :
    {p : M → G.affinePoints (CommAlgCat.of k k) //
      G.CoordinateSmooth (CommAlgCat.of k k) (RingHom.id k) I p} ≃
    {p : M → RingPoint k G.X k // RegularSmooth I p} where
  toFun p := ⟨fun t => G.affinePointsRingPointHomeomorph (CommAlgCat.of k k) (p.1 t),
    (G.regularSmooth_iff_coordinateSmooth I p.1).mpr p.2⟩
  invFun p := ⟨fun t =>
    (G.affinePointsRingPointHomeomorph (CommAlgCat.of k k)).symm (p.1 t), by
      apply (G.regularSmooth_iff_coordinateSmooth I _).mp
      simpa only [Homeomorph.apply_symm_apply] using p.2⟩
  left_inv p := by
    apply Subtype.ext
    funext t
    exact Homeomorph.symm_apply_apply _ _
  right_inv p := by
    apply Subtype.ext
    funext t
    exact Homeomorph.apply_symm_apply _ _

@[simp] theorem coordinateSmoothRegularSmoothFamilyEquiv_apply
    (p : {p : M → G.affinePoints (CommAlgCat.of k k) //
      G.CoordinateSmooth (CommAlgCat.of k k) (RingHom.id k) I p}) (t : M) :
    (G.coordinateSmoothRegularSmoothFamilyEquiv I p).1 t =
      G.affinePointsRingPointHomeomorph (CommAlgCat.of k k) (p.1 t) := rfl

@[simp] theorem coordinateSmoothRegularSmoothFamilyEquiv_symm_apply
    (p : {p : M → RingPoint k G.X k // RegularSmooth I p}) (t : M) :
    ((G.coordinateSmoothRegularSmoothFamilyEquiv I).symm p).1 t =
      (G.affinePointsRingPointHomeomorph (CommAlgCat.of k k)).symm (p.1 t) := rfl

variable {G I} in
omit [IsAffine G.X.left] in
/-- Over the identity coefficient map the coordinate criterion gives continuity
for the published actual point evaluation topology. -/
theorem CoordinateSmooth.continuous
    {p : M → G.affinePoints (CommAlgCat.of k k)}
    (hp : G.CoordinateSmooth (CommAlgCat.of k k) (RingHom.id k) I p) :
    Continuous p := by
  apply (G.continuous_affinePoints_iff (CommAlgCat.of k k) p).mpr
  intro a
  exact (hp a).continuous

local instance : Group (RingPoint k G.X k) :=
  G.ringPointGroup (CommAlgCat.of k k)

variable {G I} in
/-- The intrinsic regular-function criterion is preserved by actual inversion. -/
theorem regularSmooth_inv {p : M → RingPoint k G.X k}
    (hp : RegularSmooth I p) :
    RegularSmooth I (fun t => (p t)⁻¹) := by
  have hp' : G.CoordinateSmooth (CommAlgCat.of k k) (RingHom.id k) I
      (fun t => (G.affinePointsRingPointHomeomorph (CommAlgCat.of k k)).symm (p t)) := by
    apply (G.regularSmooth_iff_coordinateSmooth I _).mp
    simpa only [Homeomorph.apply_symm_apply] using hp
  have h := (G.regularSmooth_iff_coordinateSmooth I _).mpr hp'.inv
  have he (t : M) :
      G.affinePointsRingPointHomeomorph (CommAlgCat.of k k)
          ((G.affinePointsRingPointHomeomorph (CommAlgCat.of k k)).symm (p t))⁻¹ =
        (p t)⁻¹ := by
    exact (G.affinePointsRingPointHomeomorph_inv (CommAlgCat.of k k) _).trans
      (congrArg Inv.inv (Homeomorph.apply_symm_apply _ _))
  simpa only [he] using h

variable {G I} in
/-- The intrinsic regular-function criterion is preserved by actual multiplication. -/
theorem regularSmooth_mul {p q : M → RingPoint k G.X k}
    (hp : RegularSmooth I p) (hq : RegularSmooth I q) :
    RegularSmooth I (fun t => p t * q t) := by
  have hp' : G.CoordinateSmooth (CommAlgCat.of k k) (RingHom.id k) I
      (fun t => (G.affinePointsRingPointHomeomorph (CommAlgCat.of k k)).symm (p t)) := by
    apply (G.regularSmooth_iff_coordinateSmooth I _).mp
    simpa only [Homeomorph.apply_symm_apply] using hp
  have hq' : G.CoordinateSmooth (CommAlgCat.of k k) (RingHom.id k) I
      (fun t => (G.affinePointsRingPointHomeomorph (CommAlgCat.of k k)).symm (q t)) := by
    apply (G.regularSmooth_iff_coordinateSmooth I _).mp
    simpa only [Homeomorph.apply_symm_apply] using hq
  have h := (G.regularSmooth_iff_coordinateSmooth I _).mpr
    (CoordinateSmooth.mul G (CommAlgCat.of k k) (RingHom.id k) I hp' hq')
  have he (t : M) :
      G.affinePointsRingPointHomeomorph (CommAlgCat.of k k)
          ((G.affinePointsRingPointHomeomorph (CommAlgCat.of k k)).symm (p t) *
            (G.affinePointsRingPointHomeomorph (CommAlgCat.of k k)).symm (q t)) =
        p t * q t := by
    exact (G.affinePointsRingPointHomeomorph_mul (CommAlgCat.of k k) _ _).trans
      (congrArg₂ (· * ·) (Homeomorph.apply_symm_apply _ _)
        (Homeomorph.apply_symm_apply _ _))
  simpa only [he] using h

end Langlands.GroupScheme
