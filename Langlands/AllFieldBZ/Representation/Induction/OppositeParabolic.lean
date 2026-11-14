import Langlands.AllFieldBZ.Representation.Induction.Parabolic
import Langlands.Representation.Induction.OppositeParabolic

/-!
# All-field port of `Langlands.Representation.Induction.OppositeParabolic`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Induction.OppositeParabolic` to an arbitrary nonarchimedean local field
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
universe uF uV uW uX

variable {F : LocalFieldPackage.{uF}}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

private theorem isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The opposite induction half `δ_P^(-1/2)` of the upper block modulus. -/
def oppositeLeviHalfCharacter :
    letI := T.leviTopology B
    Induction.SmoothCharacter ℂ (B.Levi F.Carrier) :=
  letI := T.leviTopology B
  ⟨Jacquet.inverseHalfCharacter (T.leviModulus B),
    Jacquet.isOpen_ker_inverseHalfCharacter _ (T.isOpen_ker_leviModulus B)⟩

@[simp]
theorem oppositeLeviHalfCharacter_toMonoidHom :
    letI := T.leviTopology B
    (T.oppositeLeviHalfCharacter B).toMonoidHom = (T.leviHalfModulus B)⁻¹ := rfl

/-- The inverse upper half modulus inflated to the actual opposite parabolic. -/
def oppositeParabolicHalfModulus : B.oppositeParabolic F.Carrier →* ℂˣ :=
  (Jacquet.inverseHalfCharacter (T.leviModulus B)).comp
    (B.oppositeLeviProjection F.Carrier)

@[simp]
theorem oppositeParabolicHalfModulus_apply (g : B.oppositeParabolic F.Carrier) :
    T.oppositeParabolicHalfModulus B g =
      (T.leviHalfModulus B (B.oppositeLeviProjection F.Carrier g))⁻¹ := rfl

@[simp]
theorem oppositeParabolicHalfModulus_section (m : B.Levi F.Carrier) :
    T.oppositeParabolicHalfModulus B (B.oppositeLeviInParabolic F.Carrier m) =
      (T.leviHalfModulus B m)⁻¹ := by
  simp

@[simp]
theorem oppositeParabolicHalfModulus_unipotent
    (u : B.oppositeUnipotentRadical F.Carrier) :
    T.oppositeParabolicHalfModulus B u = 1 := by
  have hu : B.oppositeLeviProjection F.Carrier u = 1 := u.property
  simp [hu]

/-- Normalized parabolic induction `i_(P̄)^G σ` for an actual p-adic field: smooth
induction by right translation of `δ_P^(-1/2) ⊗ σ`, inflated to the parabolic. -/
def normalizedOppositeParabolicInduced (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F.Carrier)
      (Induction.SmoothFunctions (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B) (σ.comp (B.oppositeLeviProjection F.Carrier)))) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedOppositeInducedOf (T.oppositeLeviHalfCharacter B) σ

/-- The opposite induced representation acts by right translation. -/
@[simp]
theorem normalizedOppositeParabolicInduced_apply
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (g : GeneralLinear n F.Carrier)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          (σ.comp (B.oppositeLeviProjection F.Carrier))))
    (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          (σ.comp (B.oppositeLeviProjection F.Carrier)))
        (T.normalizedOppositeParabolicInduced B σ g f) x =
      Induction.eval (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          (σ.comp (B.oppositeLeviProjection F.Carrier))) f (x * g) := rfl

/-- The induced map of an actual Levi intertwiner. -/
def normalizedOppositeParabolicInducedMap {σ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W} (f : σ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedOppositeParabolicInduced B σ).IntertwiningMap (T.normalizedOppositeParabolicInduced B τ) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedOppositeInducedOfMap (T.oppositeLeviHalfCharacter B) f

/-- The induced map is postcomposition with the given Levi intertwiner. -/
@[simp]
theorem normalizedOppositeParabolicInducedMap_apply
    {σ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W} (f : σ.IntertwiningMap τ)
    (φ : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          (σ.comp (B.oppositeLeviProjection F.Carrier))))
    (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          (τ.comp (B.oppositeLeviProjection F.Carrier)))
        (T.normalizedOppositeParabolicInducedMap B f φ) x =
      f (Induction.eval (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          (σ.comp (B.oppositeLeviProjection F.Carrier))) φ x) := rfl

@[simp]
theorem normalizedOppositeParabolicInducedMap_id
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    T.normalizedOppositeParabolicInducedMap B (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id (T.normalizedOppositeParabolicInduced B σ) := by
  let := T.topology
  let := T.isTopologicalRing
  exact B.normalizedOppositeInducedOfMap_id (T.oppositeLeviHalfCharacter B) σ

@[simp]
theorem normalizedOppositeParabolicInducedMap_comp
    {σ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W}
    {υ : Representation ℂ (B.Levi F.Carrier) X}
    (f : σ.IntertwiningMap τ) (g : τ.IntertwiningMap υ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    T.normalizedOppositeParabolicInducedMap B (g.comp f) =
      (T.normalizedOppositeParabolicInducedMap B g).comp
        (T.normalizedOppositeParabolicInducedMap B f) := by
  let := T.topology
  let := T.isTopologicalRing
  exact B.normalizedOppositeInducedOfMap_comp (T.oppositeLeviHalfCharacter B) f g

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
namespace Langlands.AllFieldBZ.LocalFieldPackage
universe uF uV

variable (F : LocalFieldPackage.{uF})
variable {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Langlands.AllFieldBZ.LocalFieldPackage
