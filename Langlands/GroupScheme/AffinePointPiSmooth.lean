import Langlands.GroupScheme.AffinePointPiProducts
import Langlands.GroupScheme.AffinePointCoordinateSmooth
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! # Coordinate-smooth families over finite coefficient products -/

noncomputable section

universe u v w z

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} {J : Type u}
  (A : J → CommAlgCat.{u} R)
  {B : J → Type z} [∀ i, NormedCommRing (B i)] [∀ i, NormedAlgebra ℝ (B i)]
  (c : (i : J) → A i →+* B i)

/-- The product of specified coefficient maps into smooth test algebras. -/
def affinePointPiCoefficientMap : ((i : J) → A i) →+* ((i : J) → B i) :=
  RingHom.pi (fun i => (c i).comp (Pi.evalRingHom (fun i => A i) i))

omit [∀ i, NormedAlgebra ℝ (B i)] in
@[simp]
theorem affinePointPiCoefficientMap_apply (x : (i : J) → A i) (i : J) :
    affinePointPiCoefficientMap A c x i = c i (x i) := rfl

variable (G : GroupScheme (Spec R)) [IsAffine G.X.left] [Fintype J]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

omit [IsAffine G.X.left] in
/-- The original global regular-function tests over a finite coefficient product
are equivalent to their component tests on the actual projected points. -/
theorem coordinateSmooth_pi_iff
    (p : M → G.affinePoints (CommAlgCat.of R ((i : J) → A i))) :
    G.CoordinateSmooth (CommAlgCat.of R ((i : J) → A i))
        (affinePointPiCoefficientMap A c) I p ↔
      ∀ i, G.CoordinateSmooth (A i) (c i) I
        (fun x => G.affinePointsEval A i (p x)) := by
  constructor
  · intro hp i a
    have h := (contMDiff_pi_space.mp (hp a)) i
    change ContMDiff I 𝓘(ℝ, B i) ∞
      (fun x => c i (G.affinePointEvaluation
        (CommAlgCat.of R ((i : J) → A i)) (p x) a i)) at h
    simpa only [G.affinePointsEval_evaluation] using h
  · intro hp a
    apply contMDiff_pi_space.mpr
    intro i
    change ContMDiff I 𝓘(ℝ, B i) ∞
      (fun x => c i (G.affinePointEvaluation
        (CommAlgCat.of R ((i : J) → A i)) (p x) a i))
    simpa only [G.affinePointsEval_evaluation] using hp i a

/-- Assemble componentwise coordinate-smooth families using the actual point
product equivalence. -/
theorem coordinateSmooth_affinePointPi
    (p : (i : J) → M → G.affinePoints (A i))
    (hp : ∀ i, G.CoordinateSmooth (A i) (c i) I (p i)) :
    G.CoordinateSmooth (CommAlgCat.of R ((i : J) → A i))
      (affinePointPiCoefficientMap A c) I (fun x => G.affinePointPi A (fun i => p i x)) := by
  apply (coordinateSmooth_pi_iff A c G I _).mpr
  intro i
  simpa only [G.affinePointsEval_pi] using hp i

/-- The point-product decomposition identifies the original coordinate-smooth
families with dependent families of componentwise coordinate-smooth maps. -/
def coordinateSmoothPiFamilyEquiv :
    {p : M → G.affinePoints (CommAlgCat.of R ((i : J) → A i)) //
      G.CoordinateSmooth (CommAlgCat.of R ((i : J) → A i))
        (affinePointPiCoefficientMap A c) I p} ≃
    ((i : J) → {p : M → G.affinePoints (A i) //
      G.CoordinateSmooth (A i) (c i) I p}) where
  toFun p i := ⟨fun x => G.affinePointsEval A i (p.1 x),
    (coordinateSmooth_pi_iff A c G I p.1).mp p.2 i⟩
  invFun p := ⟨fun x => G.affinePointPi A (fun i => (p i).1 x),
    coordinateSmooth_affinePointPi A c G I (fun i => (p i).1) (fun i => (p i).2)⟩
  left_inv p := by
    apply Subtype.ext
    funext x
    exact G.affinePointPi_evaluations A (p.1 x)
  right_inv p := by
    funext i
    apply Subtype.ext
    funext x
    exact G.affinePointsEval_pi A (fun i => (p i).1 x) i

end Langlands.GroupScheme
