import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.AffinePointRingPointComparison
import Langlands.GroupScheme.AffinePointCoordinateSmooth
import Langlands.AlgebraicGeometry.PointManifold.AffineBaseChangeSmooth
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # Actual group points under compatible affine base change -/

noncomputable section

universe u v w z

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.AlgebraicGeometry.PointManifold

variable (C D A : Type u) [CommRing C] [CommRing D] [CommRing A]
  [Algebra C D] [Algebra C A] [Algebra D A] [IsScalarTower C D A]
  (G : GroupScheme (Spec (CommRingCat.of C)))

/-- The actual pullback-adjunction equivalence, preserving the original
categorical group laws on coefficient points. -/
def affinePointsBaseChangeMulEquiv :
    G.affinePoints (CommAlgCat.of C A) ≃*
      ((GroupScheme.baseChange (Spec.algebraMap C D)).obj G).affinePoints
        (CommAlgCat.of D A) :=
  ((baseChangePointsEquiv (Spec.algebraMap C D) G (ringTest D A)).trans
    (G.points.mapIso (ringTestRestrictScalarsIso C D A).symm.op).groupIsoToMulEquiv).symm

/-- The inverse comparison is the first projection of the actual pullback. -/
@[simp] theorem affinePointsBaseChangeMulEquiv_symm_left
    (q : ((GroupScheme.baseChange (Spec.algebraMap C D)).obj G).affinePoints
      (CommAlgCat.of D A)) :
    ((affinePointsBaseChangeMulEquiv C D A G).symm q).left =
      q.left ≫ pullback.fst G.X.hom (Spec.algebraMap C D) := by
  change 𝟙 _ ≫ (q.left ≫ pullback.fst G.X.hom (Spec.algebraMap C D)) = _
  exact Category.id_comp _

/-- The multiplicative comparison has exactly the published ring-point
base-change map as its underlying point map. -/
theorem affinePointsBaseChangeMulEquiv_eq_ringPoint
    (p : G.affinePoints (CommAlgCat.of C A)) :
    affinePointsBaseChangeMulEquiv C D A G p =
      ringPointBaseChangeEquiv C D A G.X p := by
  apply (affinePointsBaseChangeMulEquiv C D A G).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Over.OverMorphism.ext
  rw [affinePointsBaseChangeMulEquiv_symm_left, ringPointBaseChangeEquiv_left_fst]

variable [IsAffine G.X.left] [TopologicalSpace A]

private instance baseChanged_isAffine :
    IsAffine ((GroupScheme.baseChange (Spec.algebraMap C D)).obj G).X.left := by
  change IsAffine (pullback G.X.hom (Spec.algebraMap C D))
  infer_instance

local instance originalPointTopology :
    TopologicalSpace (G.affinePoints (CommAlgCat.of C A)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of C A)

local instance baseChangedPointTopology :
    TopologicalSpace
      (((GroupScheme.baseChange (Spec.algebraMap C D)).obj G).affinePoints
        (CommAlgCat.of D A)) :=
  affinePointsTopologicalSpace
    ((GroupScheme.baseChange (Spec.algebraMap C D)).obj G) (CommAlgCat.of D A)

/-- The multiplicative comparison is a homeomorphism for the original
regular-function evaluation topologies. -/
theorem isHomeomorph_affinePointsBaseChangeMulEquiv [IsTopologicalRing A] :
    IsHomeomorph (affinePointsBaseChangeMulEquiv C D A G) := by
  have he :
      (affinePointsBaseChangeMulEquiv C D A G :
        G.affinePoints (CommAlgCat.of C A) →
          ((GroupScheme.baseChange (Spec.algebraMap C D)).obj G).affinePoints
            (CommAlgCat.of D A)) =
        (affinePointsRingPointHomeomorph
          ((GroupScheme.baseChange (Spec.algebraMap C D)).obj G)
          (CommAlgCat.of D A)).symm ∘
          ringPointBaseChangeEquiv C D A G.X ∘
          G.affinePointsRingPointHomeomorph (CommAlgCat.of C A) := by
    funext p
    simp only [Function.comp_apply]
    have hs := G.affinePointsRingPointHomeomorph_apply (CommAlgCat.of C A) p
    have ht := affinePointsRingPointHomeomorph_symm_apply
      ((GroupScheme.baseChange (Spec.algebraMap C D)).obj G)
      (CommAlgCat.of D A) (ringPointBaseChangeEquiv C D A G.X p)
    exact (affinePointsBaseChangeMulEquiv_eq_ringPoint C D A G p).trans
      (ht.symm.trans (congrArg
        (fun q => (affinePointsRingPointHomeomorph
          ((GroupScheme.baseChange (Spec.algebraMap C D)).obj G)
          (CommAlgCat.of D A)).symm (ringPointBaseChangeEquiv C D A G.X q))
        hs.symm))
  rw [he]
  exact (affinePointsRingPointHomeomorph
    ((GroupScheme.baseChange (Spec.algebraMap C D)).obj G)
    (CommAlgCat.of D A)).symm.isHomeomorph.comp
      ((isHomeomorph_ringPointBaseChangeEquiv C D A G.X).comp
        (G.affinePointsRingPointHomeomorph (CommAlgCat.of C A)).isHomeomorph)

/-- The same pullback-adjunction map, bundled with both its actual group law
and the original evaluation topologies. -/
def affinePointsBaseChangeContinuousMulEquiv [IsTopologicalRing A] :
    G.affinePoints (CommAlgCat.of C A) ≃ₜ*
      ((GroupScheme.baseChange (Spec.algebraMap C D)).obj G).affinePoints
        (CommAlgCat.of D A) where
  toMulEquiv := affinePointsBaseChangeMulEquiv C D A G
  continuous_toFun := (isHomeomorph_affinePointsBaseChangeMulEquiv C D A G).continuous
  continuous_invFun :=
    ((affinePointsBaseChangeMulEquiv C D A G).toEquiv.isHomeomorph_iff.mp
      (isHomeomorph_affinePointsBaseChangeMulEquiv C D A G)).2

@[simp] theorem affinePointsBaseChangeContinuousMulEquiv_apply [IsTopologicalRing A]
    (p : G.affinePoints (CommAlgCat.of C A)) :
    affinePointsBaseChangeContinuousMulEquiv C D A G p =
      affinePointsBaseChangeMulEquiv C D A G p := rfl

variable {B : Type v} [NormedCommRing B] [NormedAlgebra ℝ B] (c : A →+* B)
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type w} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type z} [TopologicalSpace M] [ChartedSpace H M]

/-- Actual group base change preserves and reflects all regular-function
smoothness tests after the specified coefficient map. -/
theorem coordinateSmooth_baseChange_iff
    (p : M → G.affinePoints (CommAlgCat.of C A)) :
    ((GroupScheme.baseChange (Spec.algebraMap C D)).obj G).CoordinateSmooth
        (CommAlgCat.of D A) c I
        (fun x => affinePointsBaseChangeMulEquiv C D A G (p x)) ↔
      G.CoordinateSmooth (CommAlgCat.of C A) c I p := by
  have h := contMDiff_ringPoint_baseChange_iff C D A c I G.X p
  have hc (q : RingPoint C G.X A) (a : AffineCoordinateRing C G.X) :
      affineSchemePointEquiv C G.X A q a =
        G.affinePointEvaluation (CommAlgCat.of C A) q a :=
    G.affineSchemePointEquiv_evaluation (CommAlgCat.of C A) q a
  have hd (q : RingPoint D (ringBaseChange C D G.X) A)
      (a : AffineCoordinateRing D (ringBaseChange C D G.X)) :
      affineSchemePointEquiv D (ringBaseChange C D G.X) A q a =
        ((GroupScheme.baseChange (Spec.algebraMap C D)).obj G).affinePointEvaluation
          (CommAlgCat.of D A) q a :=
    affineSchemePointEquiv_evaluation
      ((GroupScheme.baseChange (Spec.algebraMap C D)).obj G) (CommAlgCat.of D A) q a
  simp_rw [hc, hd] at h
  change
    ((GroupScheme.baseChange (Spec.algebraMap C D)).obj G).CoordinateSmooth
        (CommAlgCat.of D A) c I
        (fun x => ringPointBaseChangeEquiv C D A G.X (p x)) ↔
      G.CoordinateSmooth (CommAlgCat.of C A) c I p at h
  simpa only [affinePointsBaseChangeMulEquiv_eq_ringPoint] using h

/-- The same multiplicative point comparison restricts to precisely the actual
coordinate-smooth parameter families on either group. -/
def coordinateSmoothBaseChangeFamilyEquiv :
    {p : M → G.affinePoints (CommAlgCat.of C A) //
      G.CoordinateSmooth (CommAlgCat.of C A) c I p} ≃
    {p : M →
      ((GroupScheme.baseChange (Spec.algebraMap C D)).obj G).affinePoints
        (CommAlgCat.of D A) //
      ((GroupScheme.baseChange (Spec.algebraMap C D)).obj G).CoordinateSmooth
        (CommAlgCat.of D A) c I p} where
  toFun p := ⟨fun x => affinePointsBaseChangeMulEquiv C D A G (p.1 x),
    (coordinateSmooth_baseChange_iff C D A G c I p.1).mpr p.2⟩
  invFun p := ⟨fun x => (affinePointsBaseChangeMulEquiv C D A G).symm (p.1 x), by
    apply (coordinateSmooth_baseChange_iff C D A G c I _).mp
    simpa only [MulEquiv.apply_symm_apply] using p.2⟩
  left_inv p := by
    apply Subtype.ext
    funext x
    exact (affinePointsBaseChangeMulEquiv C D A G).symm_apply_apply (p.1 x)
  right_inv p := by
    apply Subtype.ext
    funext x
    exact (affinePointsBaseChangeMulEquiv C D A G).apply_symm_apply (p.1 x)

end Langlands.GroupScheme
