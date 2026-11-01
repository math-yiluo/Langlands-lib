import Langlands.Global.AdelicParabolicInductionTopology
import Langlands.Global.AdelicGLTopology
import Mathlib.RepresentationTheory.Continuous.Basic

/-! # Joint continuity of the actual adelic section action -/

noncomputable section

universe uF uV uW

namespace Langlands.Global.AdelicParabolicInduction.CompactOpenSections

open NumberField Langlands.GeneralLinear AdelicBlockParabolic

variable (F : Type uF) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable {V : Type uV} {W : Type uW}
variable [NormedAddCommGroup V] [NormedSpace ℂ V]
variable [NormedAddCommGroup W] [NormedSpace ℂ W]
variable (σ : Representation ℂ (FullLevi F B) V)

/-- The faithful function realization sends the existing action to actual right translation. -/
theorem toContinuousMap_rightAction_eq (g : AdelicGL F n)
    (f : CompactOpenSections F B σ) :
    toContinuousMap F B σ (rightAction F B σ g f) =
      AdelicGL.rightTranslate F n g (toContinuousMap F B σ f) := by
  ext x
  rfl

/-- Both the actual adelic group element and the section vary continuously. -/
theorem continuous_rightAction_joint :
    Continuous (fun p : AdelicGL F n × CompactOpenSections F B σ =>
      rightAction F B σ p.1 p.2) := by
  apply continuous_induced_rng.mpr
  exact (AdelicGL.continuous_rightTranslate F n).comp
    (continuous_fst.prodMk
      ((isEmbedding_toContinuousMap F B σ).continuous.comp continuous_snd))

/-- Every section has a continuous full adelic orbit map. -/
theorem continuous_rightAction_orbit (f : CompactOpenSections F B σ) :
    Continuous (fun g : AdelicGL F n => rightAction F B σ g f) := by
  apply continuous_induced_rng.mpr
  exact AdelicGL.continuous_rightTranslate_orbit F n (toContinuousMap F B σ f)

/-- The section and the point of evaluation can vary simultaneously. -/
theorem continuous_evaluation :
    Continuous (fun p : CompactOpenSections F B σ × AdelicGL F n =>
      toContinuousMap F B σ p.1 p.2) :=
  (AdelicGL.continuous_evaluation F n).comp
    (((isEmbedding_toContinuousMap F B σ).continuous.comp continuous_fst).prodMk
      continuous_snd)

/-- The actual action bundled as continuous complex linear operators.
Joint action continuity is the separate theorem `continuous_rightAction_joint`. -/
def rightContRepresentation :
    ContRepresentation ℂ (AdelicGL F n) (CompactOpenSections F B σ) where
  toMonoidHom :=
    { toFun := rightTranslation F B σ
      map_one' := by
        apply ContinuousLinearMap.ext
        intro f
        exact congrArg (fun A => A f) (map_one (rightAction F B σ))
      map_mul' g h := by
        apply ContinuousLinearMap.ext
        intro f
        exact congrArg (fun A => A f) (map_mul (rightAction F B σ) g h) }

@[simp]
theorem rightContRepresentation_apply (g : AdelicGL F n)
    (f : CompactOpenSections F B σ) :
    rightContRepresentation F B σ g f = rightAction F B σ g f := rfl

@[simp]
theorem rightContRepresentation_toRepresentation :
    (rightContRepresentation F B σ).toRepresentation = rightAction F B σ := by
  ext g f
  rfl

variable {σ}

/-- Continuous coefficient postcomposition is an actual continuous intertwiner. -/
def contIntertwiningMap {τ : Representation ℂ (FullLevi F B) W}
    (T : σ.IntertwiningMap τ) (hT : Continuous T) :
    ContIntertwiningMap (rightContRepresentation F B σ)
      (rightContRepresentation F B τ) where
  __ := mapCLM F B T hT
  isIntertwining' g := by
    apply ContinuousLinearMap.ext
    intro f
    exact mapCLM_rightAction F B T hT g f

@[simp]
theorem contIntertwiningMap_apply {τ : Representation ℂ (FullLevi F B) W}
    (T : σ.IntertwiningMap τ) (hT : Continuous T)
    (f : CompactOpenSections F B σ) :
    contIntertwiningMap F B T hT f = mapCLM F B T hT f := rfl

end Langlands.Global.AdelicParabolicInduction.CompactOpenSections
