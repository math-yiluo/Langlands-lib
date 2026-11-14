import Langlands.AllFieldBZ.Group.GL.BlockModulus
import Langlands.Representation.Induction.Parabolic

/-!
# All-field port of `Langlands.Representation.Induction.Parabolic`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Induction.Parabolic` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
open scoped NNReal
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe uF uV uW uX

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
variable {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n)
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

end Langlands.AllFieldBZ.GeneralLinear.BlockShape
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uF uV uW

variable {F : LocalFieldPackage.{uF}}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private theorem isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The positive half `δ_P^(1/2)` of the explicit block modulus, as a smooth Levi
character for the selected realization. -/
def leviHalfCharacter :
    letI := T.leviTopology B
    Induction.SmoothCharacter ℂ (B.Levi F.Carrier) :=
  letI := T.leviTopology B
  ⟨T.leviHalfModulus B, T.isOpen_ker_leviHalfModulus B⟩

@[simp]
theorem leviHalfCharacter_toMonoidHom :
    letI := T.leviTopology B
    (T.leviHalfCharacter B).toMonoidHom = T.leviHalfModulus B := rfl

/-- Normalized parabolic induction `i_P^G σ` for an actual p-adic field: smooth
induction by right translation of `δ_P^(1/2) ⊗ σ`, inflated to the parabolic. -/
def normalizedParabolicInduced (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F.Carrier)
      (Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedInducedOf (T.leviHalfCharacter B) σ

/-- The covariance `f (p g) = δ_P(m)^(1/2) σ(m) f(g)` with `m` the Levi part of `p`. -/
theorem normalizedParabolicInduced_covariant (σ : Representation ℂ (B.Levi F.Carrier) V)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))))
    (g : B.parabolic F.Carrier) (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))
        f ((g : GeneralLinear n F.Carrier) * x) =
      ((NNReal.sqrt (T.leviModulus B (B.leviProjection F.Carrier g) : ℝ≥0) : ℝ) : ℂ) •
        σ (B.leviProjection F.Carrier g)
          (Induction.eval (B.parabolic F.Carrier)
            (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))) f x) :=
  f.1.2 g x

theorem isSmooth_normalizedParabolicInduced (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth (T.normalizedParabolicInduced B σ) := by
  let := T.topology
  let := T.isTopologicalRing
  exact B.isSmooth_normalizedInducedOf (T.leviHalfCharacter B) σ

/-- The induced map of an actual Levi intertwiner. -/
def normalizedParabolicInducedMap {σ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W} (f : σ.IntertwiningMap τ) :
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
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedInductionFunctorOf (T.leviHalfCharacter B)

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
namespace Langlands.AllFieldBZ.LocalFieldPackage
universe uF uV

variable (F : LocalFieldPackage.{uF})
variable {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Langlands.AllFieldBZ.LocalFieldPackage
