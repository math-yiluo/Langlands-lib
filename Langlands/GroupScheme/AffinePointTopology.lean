import Langlands.GroupScheme.AffinePoints
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Hausdorff

/-! # The coordinate-evaluation topology on actual coefficient points -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Topology

namespace Langlands.GroupScheme

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))

/-- Pullback of a global regular function, evaluated in the coefficient ring. -/
def affinePointEvaluation (A : CommAlgCat.{u} R) (x : G.affinePoints A) :
    Γ(G.X.left, ⊤) →+* A :=
  (x.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

/-- An affine scheme point is determined by all its regular-function values. -/
theorem affinePointEvaluation_injective [IsAffine G.X.left] (A : CommAlgCat.{u} R) :
    Function.Injective (fun x : G.affinePoints A => (G.affinePointEvaluation A x : _ → A)) := by
  intro x y h
  apply Over.OverMorphism.ext
  apply ext_of_isAffine
  apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of A)).hom).mp
  ext a
  exact congrFun h a

/-- The canonical topology is induced by the values of all global regular functions. -/
instance affinePointsTopologicalSpace (A : CommAlgCat.{u} R) [TopologicalSpace A] :
    TopologicalSpace ((algSpec R).obj (op A) ⟶ G.X) :=
  TopologicalSpace.induced
    (fun x : G.affinePoints A => (G.affinePointEvaluation A x : _ → A)) inferInstance

variable (A : CommAlgCat.{u} R) [TopologicalSpace A]

/-- Every regular-function evaluation is continuous in the canonical topology. -/
theorem continuous_affinePointEvaluation (a : Γ(G.X.left, ⊤)) :
    Continuous (fun x : G.affinePoints A => G.affinePointEvaluation A x a) :=
  (continuous_apply a).comp continuous_induced_dom

/-- Continuity into the point space can be checked on all regular functions. -/
theorem continuous_affinePoints_iff {T : Type v} [TopologicalSpace T]
    (f : T → G.affinePoints A) :
    Continuous f ↔ ∀ a : Γ(G.X.left, ⊤),
      Continuous (fun t => G.affinePointEvaluation A (f t) a) := by
  change Continuous[_, TopologicalSpace.induced _ _] f ↔ _
  rw [continuous_induced_rng, continuous_pi_iff]
  rfl

/-- Coordinate evaluation is a topological embedding when the group scheme is affine. -/
theorem isEmbedding_affinePointEvaluation [IsAffine G.X.left] :
    Topology.IsEmbedding
      (fun x : G.affinePoints A => (G.affinePointEvaluation A x : _ → A)) :=
  ⟨⟨rfl⟩, G.affinePointEvaluation_injective A⟩

instance affinePointsT2Space [IsAffine G.X.left] [T2Space A] :
    T2Space (G.affinePoints A) :=
  (G.isEmbedding_affinePointEvaluation A).t2Space

omit [TopologicalSpace A] in
/-- Postcomposition pulls regular functions back along the target morphism. -/
@[simp] theorem affinePointEvaluation_postcomp {H : GroupScheme (Spec R)}
    (f : G.X ⟶ H.X) (x : G.affinePoints A) (a : Γ(H.X.left, ⊤)) :
    H.affinePointEvaluation A (x ≫ f) a =
      G.affinePointEvaluation A x (f.left.appTop a) := rfl

/-- Every morphism of the underlying schemes over the base acts continuously on points. -/
theorem continuous_affinePointPostcomp {H : GroupScheme (Spec R)} (f : G.X ⟶ H.X) :
    Continuous (fun x : G.affinePoints A => x ≫ f) := by
  apply (H.continuous_affinePoints_iff A _).mpr
  intro a
  simpa only [affinePointEvaluation_postcomp] using
    G.continuous_affinePointEvaluation A (f.left.appTop a)

/-- In particular, a group-scheme homomorphism acts continuously on points. -/
theorem continuous_affinePointsTarget {H : GroupScheme (Spec R)} (f : G ⟶ H) :
    Continuous (G.affinePointsTarget f A) :=
  G.continuous_affinePointPostcomp A f.hom.hom

/-- Inversion is continuous because it is induced by the actual inverse morphism. -/
instance affinePointsContinuousInv : ContinuousInv (G.affinePoints A) where
  continuous_inv := G.continuous_affinePointPostcomp A (GrpObj.inv (X := G.X))

variable {A}

omit [TopologicalSpace A] in
set_option backward.isDefEq.respectTransparency false in
/-- Extension of coefficients applies the coefficient map to every regular-function value. -/
@[simp] theorem affinePointEvaluation_map {B : CommAlgCat.{u} R} (f : A ⟶ B)
    (x : G.affinePoints A) (a : Γ(G.X.left, ⊤)) :
    G.affinePointEvaluation B (G.affinePointMap f x) a =
      f (G.affinePointEvaluation A x a) := by
  change (x.left.appTop ≫ ((Spec.map (CommRingCat.ofHom f.hom)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom)) a = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

/-- A continuous coefficient homomorphism induces a continuous map of actual points. -/
theorem continuous_affinePointMap {B : CommAlgCat.{u} R} [TopologicalSpace B]
    (f : A ⟶ B) (hf : Continuous f) :
    Continuous (G.affinePointMap f) := by
  apply (G.continuous_affinePoints_iff B _).mpr
  intro a
  simpa only [affinePointEvaluation_map, Function.comp_def] using
    hf.comp (G.continuous_affinePointEvaluation A a)

end Langlands.GroupScheme
