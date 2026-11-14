import Langlands.Representation.Induction.OppositeParabolic
import Langlands.AllField.Group.GL.PadicOppositeBlocks
import Langlands.AllField.Representation.Induction.Parabolic
/-!
# Normalized induction from opposite block parabolics

A representation of the actual block Levi is inflated along the block projection
of the standard lower block parabolic, twisted by the inflated normalizing
character, and smoothly induced by right translation. For p-adic fields the
normalizing character is the inverse positive square root of the upper block modulus.
-/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV uW uX


end Langlands.AllField.GeneralLinear.BlockShape

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF uV uW uX

variable {F : Type uF} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

private theorem isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The opposite induction half `δ_P^(-1/2)` of the upper block modulus. -/
def oppositeLeviHalfCharacter :
    letI := T.leviTopology B
    Induction.SmoothCharacter ℂ (B.Levi F) :=
  letI := T.leviTopology B
  ⟨Jacquet.inverseHalfCharacter (T.leviModulus B),
    Jacquet.isOpen_ker_inverseHalfCharacter _ (T.isOpen_ker_leviModulus B)⟩

@[simp]
theorem oppositeLeviHalfCharacter_toMonoidHom :
    letI := T.leviTopology B
    (T.oppositeLeviHalfCharacter B).toMonoidHom = (T.leviHalfModulus B)⁻¹ := rfl

/-- The inverse upper half modulus inflated to the actual opposite parabolic. -/
def oppositeParabolicHalfModulus : B.oppositeParabolic F →* ℂˣ :=
  (Jacquet.inverseHalfCharacter (T.leviModulus B)).comp
    (B.oppositeLeviProjection F)

@[simp]
theorem oppositeParabolicHalfModulus_apply (g : B.oppositeParabolic F) :
    T.oppositeParabolicHalfModulus B g =
      (T.leviHalfModulus B (B.oppositeLeviProjection F g))⁻¹ := rfl

theorem isOpen_ker_oppositeParabolicHalfModulus :
    letI := T.topology
    IsOpen ((T.oppositeParabolicHalfModulus B).ker :
      Set (B.oppositeParabolic F)) := by
  let := T.topology
  exact (Jacquet.isOpen_ker_inverseHalfCharacter _
    (T.isOpen_ker_leviModulus B)).preimage (T.oppositeBlockLeviProjection B).continuous

/-- Normalized parabolic induction `i_(P̄)^G σ` for an actual p-adic field: smooth
induction by right translation of `δ_P^(-1/2) ⊗ σ`, inflated to the parabolic. -/
def normalizedOppositeParabolicInduced (σ : Representation ℂ (B.Levi F) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F)
      (Induction.SmoothFunctions (B.oppositeParabolic F)
        (twist (T.oppositeParabolicHalfModulus B) (σ.comp (B.oppositeLeviProjection F)))) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedOppositeInducedOf (T.oppositeLeviHalfCharacter B) σ

/-- The covariance `f (p g) = δ_P(m)^(-1/2) σ(m) f(g)` with `m` the Levi part of `p`. -/
theorem normalizedOppositeParabolicInduced_covariant (σ : Representation ℂ (B.Levi F) V)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.oppositeParabolic F)
        (twist (T.oppositeParabolicHalfModulus B) (σ.comp (B.oppositeLeviProjection F))))
    (g : B.oppositeParabolic F) (x : GeneralLinear n F) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.oppositeParabolic F)
        (twist (T.oppositeParabolicHalfModulus B) (σ.comp (B.oppositeLeviProjection F)))
        f ((g : GeneralLinear n F) * x) =
      (((NNReal.sqrt (T.leviModulus B (B.oppositeLeviProjection F g) : ℝ≥0) : ℝ) : ℂ))⁻¹ •
        σ (B.oppositeLeviProjection F g)
          (Induction.eval (B.oppositeParabolic F)
            (twist (T.oppositeParabolicHalfModulus B) (σ.comp (B.oppositeLeviProjection F))) f x) :=
  by
    have h := f.1.2 g x
    change f.1.1 _ =
      (Jacquet.inverseHalfCharacter (T.leviModulus B)
        (B.oppositeLeviProjection F g) : ℂ) •
        σ (B.oppositeLeviProjection F g) (f.1.1 x) at h
    rw [Jacquet.inverseHalfCharacter_apply] at h
    exact h

/-- The opposite induced representation acts by right translation. -/
@[simp]
theorem normalizedOppositeParabolicInduced_apply
    (σ : Representation ℂ (B.Levi F) V)
    (g : GeneralLinear n F)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.oppositeParabolic F)
        (twist (T.oppositeParabolicHalfModulus B)
          (σ.comp (B.oppositeLeviProjection F))))
    (x : GeneralLinear n F) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.oppositeParabolic F)
        (twist (T.oppositeParabolicHalfModulus B)
          (σ.comp (B.oppositeLeviProjection F)))
        (T.normalizedOppositeParabolicInduced B σ g f) x =
      Induction.eval (B.oppositeParabolic F)
        (twist (T.oppositeParabolicHalfModulus B)
          (σ.comp (B.oppositeLeviProjection F))) f (x * g) := rfl

theorem isSmooth_normalizedOppositeParabolicInduced (σ : Representation ℂ (B.Levi F) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth (T.normalizedOppositeParabolicInduced B σ) := by
  let := T.topology
  let := T.isTopologicalRing
  exact B.isSmooth_normalizedOppositeInducedOf (T.oppositeLeviHalfCharacter B) σ

end Langlands.LocalFieldData

namespace Langlands

universe uF uV


end Langlands
