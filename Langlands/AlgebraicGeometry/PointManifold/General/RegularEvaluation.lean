import Langlands.AlgebraicGeometry.PointManifold.RegularEvaluation
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! # Universe-general regular-function values on actual affine points -/

noncomputable section

universe u v w z

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped Manifold ContDiff

namespace Langlands.AlgebraicGeometry.PointManifold.General

open PointTopology

variable {k : Type u} [RCLike k]
variable {X Y : Over (Spec (CommRingCat.of k))} [IsAffine X.left] [IsAffine Y.left]

/-- Evaluation of global regular functions at an actual relative point. -/
def regularEvaluation (p : RingPoint k X k) : AffineCoordinateRing k X →ₐ[k] k :=
  (affineSchemePointEquiv k X k p).toAlgHom

/-- Evaluation is the actual pullback on global sections, followed by `Γ(Spec k) ≅ k`. -/
theorem regularEvaluation_eq_pullback (p : RingPoint k X k) :
    (regularEvaluation p).toRingHom =
      (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom := by
  dsimp only [RingPoint] at p
  have h : CommRingCat.ofHom (regularEvaluation p).toRingHom =
      p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom := by
    apply Spec.map_injective
    let g : Spec (CommRingCat.of k) ⟶ X.left := p.left
    change Spec.map (Spec.preimage (g ≫ X.left.isoSpec.hom)) =
      Spec.map (g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom)
    rw [Spec.map_preimage, Spec.map_comp,
      ← Scheme.isoSpec_Spec_hom, ← Scheme.isoSpec_hom_naturality]
  exact congrArg (fun f => f.hom) h

theorem continuous_regularEvaluation (a : AffineCoordinateRing k X) :
    Continuous (fun p : RingPoint k X k => regularEvaluation p a) :=
  (AlgPoint.continuous_eval a).comp (affineSchemePointHomeomorph k X k).continuous

/-- The published affine topology is characterized by actual regular-function values. -/
theorem continuous_iff_regularEvaluation {T : Type*} [TopologicalSpace T]
    (f : T → RingPoint k X k) :
    Continuous f ↔ ∀ a : AffineCoordinateRing k X,
      Continuous (fun t => regularEvaluation (f t) a) := by
  rw [(affineSchemePointHomeomorph k X k).isInducing.continuous_iff,
    AlgPoint.continuous_iff]
  rfl

@[simp] theorem regularEvaluation_postcomp (f : X ⟶ Y) (p : RingPoint k X k)
    (a : AffineCoordinateRing k Y) :
    regularEvaluation (p ≫ f) a =
      regularEvaluation p (affineCoordinatePullback k f a) := by
  exact congrArg (fun q : AlgPoint k (AffineCoordinateRing k Y) k => q a)
    (affineSchemePointEquiv_natural k k f p)

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type w} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type z} [TopologicalSpace M] [ChartedSpace H M]

/-- A test property of parameter families; this assigns no manifold to the target. -/
def RegularSmooth (f : M → RingPoint k X k) : Prop :=
  ∀ a : AffineCoordinateRing k X,
    ContMDiff I 𝓘(ℝ, k) ∞ (fun t => regularEvaluation (f t) a)

theorem regularSmooth_const (p : RingPoint k X k) :
    RegularSmooth I (fun _ : M => p) :=
  fun _ => contMDiff_const

variable {I} in
theorem RegularSmooth.postcomp {f : M → RingPoint k X k} (hf : RegularSmooth I f)
    (g : X ⟶ Y) : RegularSmooth I (fun t => f t ≫ g) := by
  intro a
  simpa only [regularEvaluation_postcomp] using hf (affineCoordinatePullback k g a)

/-- The new evaluation specializes to the published Type 0 evaluation. -/
@[simp] theorem regularEvaluation_typeZero {k : Type} [RCLike k]
    {X : Over (Spec (CommRingCat.of k))} [IsAffine X.left]
    (p : RingPoint k X k) :
    regularEvaluation p = PointManifold.regularEvaluation p := rfl

/-- The family test specializes to the published test, with independent source universes. -/
theorem regularSmooth_typeZero_iff {k : Type} [RCLike k]
    {X : Over (Spec (CommRingCat.of k))} [IsAffine X.left]
    (f : M → RingPoint k X k) :
    RegularSmooth I f ↔ PointManifold.RegularSmooth I f := Iff.rfl

end Langlands.AlgebraicGeometry.PointManifold.General
