import Langlands.Representation.Hecke.IntegratedConvolution
import Langlands.Algebra.CompatibleNonUnitalAction

/-! # Group intertwiners as maps of the actual integrated Hecke actions -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Hecke

open MeasureTheory MeasureTheory.Measure

universe uG uV uW uP

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {P : Type uP} [AddCommGroup P] [Module ℂ P]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsMulLeftInvariant μ]
variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
variable {τ : Representation ℂ G P}

/-- Retain the original linear map and integrate its group intertwining law. -/
def heckeActionIntertwiner (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (T : ρ.IntertwiningMap σ) :
    Algebra.LinearIntertwiner (heckeAction μ ρ hρ) (heckeAction μ σ hσ) where
  toLinearMap := T.toLinearMap
  map_action' f v := integratedAction_intertwiner μ hρ hσ T f v

@[simp]
theorem heckeActionIntertwiner_toLinearMap (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (T : ρ.IntertwiningMap σ) :
    (heckeActionIntertwiner μ hρ hσ T).toLinearMap = T.toLinearMap := rfl

@[simp]
theorem heckeActionIntertwiner_apply (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (T : ρ.IntertwiningMap σ) (v : V) :
    heckeActionIntertwiner μ hρ hσ T v = T v := rfl

/-- Integration preserves the identity map on the original carrier. -/
@[simp]
theorem heckeActionIntertwiner_id (hρ : IsSmooth ρ) :
    heckeActionIntertwiner μ hρ hρ (Representation.IntertwiningMap.id ρ) =
      Algebra.LinearIntertwiner.id (heckeAction μ ρ hρ) := by
  apply Algebra.LinearIntertwiner.ext
  intro v
  rfl

/-- Integration preserves composition of the original group intertwiners. -/
theorem heckeActionIntertwiner_comp (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (hτ : IsSmooth τ) (T : ρ.IntertwiningMap σ) (U : σ.IntertwiningMap τ) :
    heckeActionIntertwiner μ hρ hτ (U.comp T) =
      (heckeActionIntertwiner μ hσ hτ U).comp (heckeActionIntertwiner μ hρ hσ T) := by
  apply Algebra.LinearIntertwiner.ext
  intro v
  rfl

/-- Bundling the integrated law does not identify distinct original maps. -/
theorem heckeActionIntertwiner_injective (hρ : IsSmooth ρ) (hσ : IsSmooth σ) :
    Function.Injective (heckeActionIntertwiner μ hρ hσ) := by
  intro T U h
  apply Representation.IntertwiningMap.ext
  exact congrArg Algebra.LinearIntertwiner.toLinearMap h

end Langlands.Hecke
