import Langlands.GroupScheme.AffinePointCoordinateSmooth
import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Basic

/-! # Functions tested on coordinate-smooth families of actual points -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.GroupScheme

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
  (A : CommAlgCat.{u} R)
  {B : Type u} [NormedCommRing B] [NormedAlgebra ℝ B] (c : A →+* B)

/-- A complex function on actual points is plot-smooth if it is smooth along
every coordinate-smooth family with an ordinary real normed-space model.
The quantifiers use the coefficient universe. No manifold on the point group
is assumed or assigned by this predicate. -/
def IsPlotSmooth (f : G.affinePoints A → ℂ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    (p : M → G.affinePoints A),
    G.CoordinateSmooth A c 𝓘(ℝ, E) p →
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (fun x => f (p x))

/-- Plot-smooth functions form an actual complex submodule of all functions. -/
def plotSmoothFunctions : Submodule ℂ (G.affinePoints A → ℂ) where
  carrier := {f | G.IsPlotSmooth A c f}
  zero_mem' := by
    intro E _ _ M _ _ p hp
    exact contMDiff_const
  add_mem' hf hg := by
    intro E _ _ M _ _ p hp
    exact (hf E M p hp).add (hg E M p hp)
  smul_mem' z f hf := by
    intro E _ _ M _ _ p hp
    exact (((ContinuousLinearMap.mul ℝ ℂ) z).contDiff.contMDiff).comp (hf E M p hp)

theorem isPlotSmooth_const (z : ℂ) :
    G.IsPlotSmooth A c (fun _ => z) := by
  intro E _ _ M _ _ p hp
  exact contMDiff_const

/-- A regular evaluation followed by a real continuous linear functional
is plot-smooth directly from the defining coordinate tests. -/
theorem isPlotSmooth_evaluation (a : Γ(G.X.left, ⊤)) (l : B →L[ℝ] ℂ) :
    G.IsPlotSmooth A c (fun x => l (c (G.affinePointEvaluation A x a))) := by
  intro E _ _ M _ _ p hp
  exact l.contDiff.contMDiff.comp (hp a)

variable {G A c} in
/-- Pullback by an actual regular map preserves plot-smooth functions. -/
theorem IsPlotSmooth.postcomp {H : GroupScheme (Spec R)}
    {f : H.affinePoints A → ℂ} (hf : H.IsPlotSmooth A c f)
    (φ : G.X ⟶ H.X) :
    G.IsPlotSmooth A c (fun x => f (x ≫ φ)) := by
  intro E _ _ M _ _ p hp
  exact hf E M _ (hp.postcomp φ)

variable [IsAffine G.X.left]

theorem IsPlotSmooth.rightTranslate {f : G.affinePoints A → ℂ}
    (hf : G.IsPlotSmooth A c f) (g : G.affinePoints A) :
    G.IsPlotSmooth A c (fun x => f (x * g)) := by
  intro E _ _ M _ _ p hp
  exact hf E M _ (CoordinateSmooth.mul G A c 𝓘(ℝ, E) hp
    (coordinateSmooth_const G A c 𝓘(ℝ, E) g))

theorem IsPlotSmooth.leftTranslate {f : G.affinePoints A → ℂ}
    (hf : G.IsPlotSmooth A c f) (g : G.affinePoints A) :
    G.IsPlotSmooth A c (fun x => f (g * x)) := by
  intro E _ _ M _ _ p hp
  exact hf E M _ (CoordinateSmooth.mul G A c 𝓘(ℝ, E)
    (coordinateSmooth_const G A c 𝓘(ℝ, E) g) hp)

/-- Positive right translation on the actual plot-smooth function space. -/
def plotSmoothRightAction :
    Representation ℂ (G.affinePoints A) ↥(G.plotSmoothFunctions A c) where
  toFun g :=
    { toFun f := ⟨fun x => f.val (x * g),
        IsPlotSmooth.rightTranslate G A c f.property g⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    ext f x
    exact congrArg f.val (mul_one x)
  map_mul' g h := by
    ext f x
    exact congrArg f.val (mul_assoc x g h).symm

@[simp]
theorem plotSmoothRightAction_apply (g x : G.affinePoints A)
    (f : ↥(G.plotSmoothFunctions A c)) :
    (G.plotSmoothRightAction A c g f).val x = f.val (x * g) := rfl

end Langlands.GroupScheme
