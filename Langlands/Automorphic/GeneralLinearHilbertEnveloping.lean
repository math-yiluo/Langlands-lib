import Langlands.Algebra.ComplexLieExtension
import Langlands.Global.ArchimedeanOrbitDerivativeInterchange
import Langlands.Representation.Archimedean.SmoothLieActionUnits
import Langlands.Representation.Archimedean.UnitaryRegularizationGraph
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # The enveloping action on genuine archimedean smooth Hilbert vectors -/

noncomputable section

open scoped Classical Manifold ContDiff Matrix.Norms.Operator InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 40000

namespace Langlands.Archimedean

private theorem inner_smoothLieDerivative_units
    {B E : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (R : Bˣ →* (E →L[ℂ] E))
    (hU : ∀ g x y, inner ℂ (R g x) (R g y) = inner ℂ x y)
    (X : B) (v w : smoothVectors 𝓘(ℝ, B) R) :
    inner ℂ (smoothLieDerivative 𝓘(ℝ, B) R X v : E) w =
      -inner ℂ (v : E) (smoothLieDerivative 𝓘(ℝ, B) R X w : E) := by
  apply eq_neg_of_add_eq_zero_left
  let a : E := v.val
  let b : E := w.val
  let f := orbitMap R a
  let k := orbitMap R b
  have hf : MDifferentiableAt 𝓘(ℝ, B) 𝓘(ℝ, E) f (1 : Bˣ) :=
    v.property.mdifferentiableAt (by simp)
  have hk : MDifferentiableAt 𝓘(ℝ, B) 𝓘(ℝ, E) k (1 : Bˣ) :=
    w.property.mdifferentiableAt (by simp)
  let p : Bˣ → E × E := fun g => (f g, k g)
  let q : E × E → ℂ := fun z => inner ℂ z.1 z.2
  have hq : HasMFDerivAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℂ) q (p 1)
      (fderivInnerCLM ℂ (p 1)) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (isBoundedBilinearMap_inner (𝕜 := ℂ) (E := E)).hasFDerivAt (p 1) |>.hasMFDerivAt
  have he : q ∘ p = fun _ : Bˣ => inner ℂ a b := funext fun g => hU g a b
  have hp : MDifferentiableAt 𝓘(ℝ, B) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) p (1 : Bˣ) := hf.prodMk hk
  have h := mfderiv_comp (1 : Bˣ) hq.mdifferentiableAt hp
  have hp' : mfderiv 𝓘(ℝ, B) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) p (1 : Bˣ) =
      (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) f (1 : Bˣ)).prod (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) k (1 : Bˣ)) :=
    mfderiv_prodMk hf hk
  rw [he, mfderiv_const, hq.mfderiv, hp'] at h
  have h1 : p 1 = (a, b) := by simp [p, f, k, orbitMap]
  have hX := congrArg (fun T : B →L[ℝ] ℂ => T X) h.symm
  change fderivInnerCLM ℂ (p 1)
    (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) f (1 : Bˣ) X, mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) k (1 : Bˣ) X) = 0 at hX
  simpa only [h1, fderivInnerCLM_apply, add_comm, f, k, a, b,
    smoothLieDerivative_apply, lieDerivative] using hX

end Langlands.Archimedean

namespace Langlands.Global.ArchimedeanGL

open Langlands.Archimedean DerivativeSmoothVectors

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local notation "A" => ArchimedeanMatrix F n
local notation "I" => 𝓘(ℝ, A)

variable (R : (ArchimedeanMatrix F n)ˣ →* (E →L[ℂ] E))

local notation "D" => DerivativeSmoothVectors I R

include R

/-- The value in the Hilbert space of a vector of the genuine smooth carrier. -/
def hilbertSmoothValue : D →ₗ[ℂ] E :=
  (Langlands.Archimedean.smoothVectors I R).subtype.comp (toSmooth I R).toLinearMap

private def hilbertRealLieAction (hR : IsContinuousRepresentation R) :
    RealLieAlgebra F n →ₗ⁅ℝ⁆ Module.End ℂ D :=
  { toLinearMap := (operatorDirection R).comp (realLieAlgebraToMatrix F n).toLinearMap
    map_lie' {X Y} := by
      apply LinearMap.ext
      intro v
      change operator I R (realLieAlgebraToMatrix F n ⁅X, Y⁆) v =
        operator I R (realLieAlgebraToMatrix F n X) (operator I R (realLieAlgebraToMatrix F n Y) v) -
        operator I R (realLieAlgebraToMatrix F n Y) (operator I R (realLieAlgebraToMatrix F n X) v)
      rw [realLieAlgebraToMatrix_lie, operator_commutator_units R hR] }

/-- The universal enveloping action extending the actual Hilbert orbit derivatives. -/
def hilbertEnvelopingAction (hR : IsContinuousRepresentation R) :
    EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ D := by
  exact Langlands.Algebra.ComplexLieExtension.enveloping (hilbertRealLieAction F n R hR)

@[simp]
theorem hilbertEnvelopingAction_real_generator (hR : IsContinuousRepresentation R)
    (X : RealLieAlgebra F n) :
    hilbertEnvelopingAction F n R hR (envelopingGenerator F n (complexify F n X)) =
      operator I R (realLieAlgebraToMatrix F n X) := by
  exact Langlands.Algebra.ComplexLieExtension.enveloping_real_generator
    (hilbertRealLieAction F n R hR) X

/-- Each genuine enveloping operator has a formal adjoint on the same smooth carrier. -/
theorem exists_hilbertEnvelopingAction_formalAdjoint (hR : IsContinuousRepresentation R)
    (hU : ∀ g x y, inner ℂ (R g x) (R g y) = inner ℂ x y)
    (a : EnvelopingAlgebra F n) :
    ∃ T : Module.End ℂ D, ∀ v w,
      inner ℂ (hilbertSmoothValue F n R (hilbertEnvelopingAction F n R hR a v))
        (hilbertSmoothValue F n R w) =
      inner ℂ (hilbertSmoothValue F n R v) (hilbertSmoothValue F n R (T w)) := by
  let e := hilbertSmoothValue F n R
  let ρ := hilbertEnvelopingAction F n R hR
  change ∃ T : Module.End ℂ D, ∀ v w, inner ℂ (e (ρ a v)) (e w) = inner ℂ (e v) (e (T w))
  induction a using enveloping_real_left_induction F n with
  | h1 => exact ⟨1, by simp⟩
  | hadd a b ha hb =>
    obtain ⟨Sa, ha⟩ := ha
    obtain ⟨Sb, hb⟩ := hb
    exact ⟨Sa + Sb, by simp [inner_add_left, inner_add_right, ha, hb]⟩
  | hsmul z a ha =>
    obtain ⟨T, hT⟩ := ha
    exact ⟨star z • T, by simp [inner_smul_left, inner_smul_right, hT]⟩
  | hgen X a ha =>
    obtain ⟨T, hT⟩ := ha
    refine ⟨-(T * operator I R (realLieAlgebraToMatrix F n X)), fun v w => ?_⟩
    have hgen : ρ (envelopingGenerator F n (complexify F n X)) =
        operator I R (realLieAlgebraToMatrix F n X) := hilbertEnvelopingAction_real_generator F n R hR X
    rw [map_mul, Module.End.mul_apply, hgen]
    rw [show inner ℂ (e (operator I R (realLieAlgebraToMatrix F n X) (ρ a v))) (e w) =
      -inner ℂ (e (ρ a v)) (e (operator I R (realLieAlgebraToMatrix F n X) w)) from
      inner_smoothLieDerivative_units R hU _ (toSmooth I R (ρ a v)) (toSmooth I R w), hT]
    simp only [LinearMap.neg_apply, Module.End.mul_apply, map_neg, inner_neg_right]

end Langlands.Global.ArchimedeanGL
