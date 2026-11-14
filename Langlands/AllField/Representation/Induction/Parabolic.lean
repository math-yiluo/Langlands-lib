import Langlands.Representation.Induction.Parabolic
import Langlands.AllField.Group.GL.BlockModulusSupplement
/-!
# Normalized parabolic induction from standard block Levi subgroups

A representation of the actual block Levi is inflated along the block projection
of the standard upper block parabolic, twisted by the inflated normalizing
character, and smoothly induced by right translation. For p-adic fields the
normalizing character is the positive square root of the explicit block modulus.
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

universe uF uV uW

variable {F : Type uF} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private theorem isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The positive half `δ_P^(1/2)` of the explicit block modulus, as a smooth Levi
character for the selected realization. -/
def leviHalfCharacter :
    letI := T.leviTopology B
    Induction.SmoothCharacter ℂ (B.Levi F) :=
  letI := T.leviTopology B
  ⟨T.leviHalfModulus B, T.isOpen_ker_leviHalfModulus B⟩

@[simp]
theorem leviHalfCharacter_toMonoidHom :
    letI := T.leviTopology B
    (T.leviHalfCharacter B).toMonoidHom = T.leviHalfModulus B := rfl

/-- Normalized parabolic induction `i_P^G σ` for an actual p-adic field: smooth
induction by right translation of `δ_P^(1/2) ⊗ σ`, inflated to the parabolic. -/
def normalizedParabolicInduced (σ : Representation ℂ (B.Levi F) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F)
      (Induction.SmoothFunctions (B.parabolic F)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F)))) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedInducedOf (T.leviHalfCharacter B) σ

/-- The covariance `f (p g) = δ_P(m)^(1/2) σ(m) f(g)` with `m` the Levi part of `p`. -/
theorem normalizedParabolicInduced_covariant (σ : Representation ℂ (B.Levi F) V)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F))))
    (g : B.parabolic F) (x : GeneralLinear n F) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.parabolic F)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F)))
        f ((g : GeneralLinear n F) * x) =
      ((NNReal.sqrt (T.leviModulus B (B.leviProjection F g) : ℝ≥0) : ℝ) : ℂ) •
        σ (B.leviProjection F g)
          (Induction.eval (B.parabolic F)
            (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F))) f x) :=
  f.1.2 g x

theorem isSmooth_normalizedParabolicInduced (σ : Representation ℂ (B.Levi F) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth (T.normalizedParabolicInduced B σ) := by
  let := T.topology
  let := T.isTopologicalRing
  exact B.isSmooth_normalizedInducedOf (T.leviHalfCharacter B) σ

/-- The induced map of an actual Levi intertwiner. -/
def normalizedParabolicInducedMap {σ : Representation ℂ (B.Levi F) V}
    {τ : Representation ℂ (B.Levi F) W} (f : σ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedParabolicInduced B σ).IntertwiningMap (T.normalizedParabolicInduced B τ) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedInducedOfMap (T.leviHalfCharacter B) f

/-- Normalized parabolic induction as a functor of canonical smooth categories. -/
def normalizedParabolicInductionFunctor :
    letI := T.leviTopology B
    letI := T.generalLinearTopology n
    SmoothRep.{0, uF, uV} ℂ (B.Levi F) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedInductionFunctorOf (T.leviHalfCharacter B)

end Langlands.LocalFieldData

namespace Langlands

universe uF uV


end Langlands
