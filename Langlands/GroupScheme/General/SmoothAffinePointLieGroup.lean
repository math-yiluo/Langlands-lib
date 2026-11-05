import Langlands.AlgebraicGeometry.PointManifold.General.SmoothAffineManifold
import Langlands.GroupScheme.AffinePointRingPointComparison
import Langlands.GroupScheme.AffinePointCoordinateSmooth
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! # The original point group on the universe-general chosen affine manifold -/

noncomputable section

universe u v w

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped Manifold ContDiff CategoryTheory.MonObj

namespace Langlands.GroupScheme.General

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.AlgebraicGeometry.PointManifold.General

section RegularFamilies

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [RCLike k]
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

local instance : Group (RingPoint k G.X k) :=
  G.ringPointGroup (CommAlgCat.of k k)

variable {G I} in
/-- The intrinsic regular-function criterion is preserved by actual inversion. -/
theorem regularSmooth_inv {p : M → RingPoint k G.X k}
    (hp : RegularSmooth I p) :
    RegularSmooth I (fun t => (p t)⁻¹) := by
  have hp' : G.CoordinateSmooth (CommAlgCat.of k k) (RingHom.id k) I
      (fun t => (G.affinePointsRingPointHomeomorph (CommAlgCat.of k k)).symm (p t)) := by
    apply (regularSmooth_iff_coordinateSmooth G I _).mp
    simpa only [Homeomorph.apply_symm_apply] using hp
  have h := (regularSmooth_iff_coordinateSmooth G I _).mpr hp'.inv
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
    apply (regularSmooth_iff_coordinateSmooth G I _).mp
    simpa only [Homeomorph.apply_symm_apply] using hp
  have hq' : G.CoordinateSmooth (CommAlgCat.of k k) (RingHom.id k) I
      (fun t => (G.affinePointsRingPointHomeomorph (CommAlgCat.of k k)).symm (q t)) := by
    apply (regularSmooth_iff_coordinateSmooth G I _).mp
    simpa only [Homeomorph.apply_symm_apply] using hq
  have h := (regularSmooth_iff_coordinateSmooth G I _).mpr
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


end RegularFamilies

section Atlas

variable {k : Type u} [RCLike k]
variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
variable {d : ℕ}

local instance : Group (RingPoint k G.X k) :=
  G.ringPointGroup (CommAlgCat.of k k)

/-- A regular atlas gives the original
actual point group a real smooth Lie group structure, on its existing topology. -/
theorem regularAtlasLieGroup (A : RegularAtlas k G.X d) :
    letI := A.chartedSpace
    LieGroup 𝓘(ℝ, Fin d → k) ∞ (RingPoint k G.X k) := by
  let := A.chartedSpace
  let : IsManifold 𝓘(ℝ, Fin d → k) ∞ (RingPoint k G.X k) := A.isManifold
  refine { toIsManifold := inferInstance, contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · apply (A.contMDiff_iff_regularSmooth (𝓘(ℝ, Fin d → k).prod 𝓘(ℝ, Fin d → k)) _).mpr
    apply regularSmooth_mul (G := G)
    · exact (A.contMDiff_iff_regularSmooth (𝓘(ℝ, Fin d → k).prod 𝓘(ℝ, Fin d → k)) _).mp
        contMDiff_fst
    · exact (A.contMDiff_iff_regularSmooth (𝓘(ℝ, Fin d → k).prod 𝓘(ℝ, Fin d → k)) _).mp
        contMDiff_snd
  · apply (A.contMDiff_iff_regularSmooth 𝓘(ℝ, Fin d → k) _).mpr
    apply regularSmooth_inv (G := G)
    exact (A.contMDiff_iff_regularSmooth 𝓘(ℝ, Fin d → k) _).mp contMDiff_id


end Atlas

section Named

variable {k : Type u} [RCLike k]
variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
variable {d : ℕ}

local instance : Group (RingPoint k G.X k) :=
  G.ringPointGroup (CommAlgCat.of k k)

/-- The group-point alias is exactly the chosen general affine charted space. -/
abbrev smoothAffineGroupChartedSpace
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    ChartedSpace (Fin d → k) (RingPoint k G.X k) :=
  smoothAffineChartedSpace hsmooth

/-- The original point group is a Lie group for the named chosen charts. -/
theorem smoothAffineLieGroup
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := smoothAffineChartedSpace hsmooth
    LieGroup 𝓘(ℝ, Fin d → k) ∞ (RingPoint k G.X k) :=
  regularAtlasLieGroup G (smoothAffineRegularAtlas hsmooth)

/-- Actual point multiplication is smooth for these same chosen charts. -/
theorem smoothAffine_contMDiff_mul
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := smoothAffineChartedSpace hsmooth
    ContMDiff (𝓘(ℝ, Fin d → k).prod 𝓘(ℝ, Fin d → k))
      𝓘(ℝ, Fin d → k) ∞
      (fun p : RingPoint k G.X k × RingPoint k G.X k => p.1 * p.2) := by
  let := smoothAffineChartedSpace hsmooth
  exact (smoothAffineLieGroup G hsmooth).contMDiff_mul

/-- Actual point inversion is smooth for these same chosen charts. -/
theorem smoothAffine_contMDiff_inv
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := smoothAffineChartedSpace hsmooth
    ContMDiff 𝓘(ℝ, Fin d → k) 𝓘(ℝ, Fin d → k) ∞
      (fun p : RingPoint k G.X k => p⁻¹) := by
  let := smoothAffineChartedSpace hsmooth
  exact (smoothAffineLieGroup G hsmooth).contMDiff_inv

/-- The real point group uses the chosen real charts and the original group law. -/
theorem realSmoothAffineLieGroup
    (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left] (d : ℕ)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := realSmoothAffineChartedSpace G.X d hsmooth
    LieGroup 𝓘(ℝ, Fin d → ℝ) ∞ (RingPoint ℝ G.X ℝ) :=
  smoothAffineLieGroup G hsmooth

/-- The complex point group is a real Lie group on the chosen complex charts. -/
theorem complexSmoothAffineLieGroup
    (G : GroupScheme (Spec (CommRingCat.of ℂ))) [IsAffine G.X.left] (d : ℕ)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := complexSmoothAffineChartedSpace G.X d hsmooth
    LieGroup 𝓘(ℝ, Fin d → ℂ) ∞ (RingPoint ℂ G.X ℂ) :=
  smoothAffineLieGroup G hsmooth

local instance : TopologicalSpace (G.affinePoints (CommAlgCat.of k k)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of k k)

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- For the named chosen manifold, the family criterion is exactly the original
identity-coefficient coordinate criterion under the actual-carrier homeomorphism. -/
theorem smoothAffine_contMDiff_iff_coordinateSmooth
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (p : M → G.affinePoints (CommAlgCat.of k k)) :
    letI := smoothAffineChartedSpace hsmooth
    ContMDiff I 𝓘(ℝ, Fin d → k) ∞
        (fun t => G.affinePointsRingPointHomeomorph (CommAlgCat.of k k) (p t)) ↔
      G.CoordinateSmooth (CommAlgCat.of k k) (RingHom.id k) I p :=
  (smoothAffine_contMDiff_iff_regularSmooth.{u, v, v, w} I hsmooth _).trans
    (regularSmooth_iff_coordinateSmooth G I p)

/-- The chosen real point manifold has the identity-coefficient family criterion. -/
theorem realSmoothAffine_contMDiff_iff_coordinateSmooth
    (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left] (d : ℕ)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (p : M → G.affinePoints (CommAlgCat.of ℝ ℝ)) :
    letI := realSmoothAffineChartedSpace G.X d hsmooth
    ContMDiff I 𝓘(ℝ, Fin d → ℝ) ∞
        (fun t => G.affinePointsRingPointHomeomorph (CommAlgCat.of ℝ ℝ) (p t)) ↔
      G.CoordinateSmooth (CommAlgCat.of ℝ ℝ) (RingHom.id ℝ) I p :=
  smoothAffine_contMDiff_iff_coordinateSmooth G I hsmooth p

/-- The chosen complex point manifold has the real smooth family criterion. -/
theorem complexSmoothAffine_contMDiff_iff_coordinateSmooth
    (G : GroupScheme (Spec (CommRingCat.of ℂ))) [IsAffine G.X.left] (d : ℕ)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (p : M → G.affinePoints (CommAlgCat.of ℂ ℂ)) :
    letI := complexSmoothAffineChartedSpace G.X d hsmooth
    ContMDiff I 𝓘(ℝ, Fin d → ℂ) ∞
        (fun t => G.affinePointsRingPointHomeomorph (CommAlgCat.of ℂ ℂ) (p t)) ↔
      G.CoordinateSmooth (CommAlgCat.of ℂ ℂ) (RingHom.id ℂ) I p :=
  smoothAffine_contMDiff_iff_coordinateSmooth G I hsmooth p


end Named

end Langlands.GroupScheme.General
