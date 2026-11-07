import Langlands.LocalFactor.CommonClosureSurjectivity
import Langlands.LocalFactor.DeligneHenniartStatement

/-! # Algebra of actual Deligne--Henniart witnesses -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open CommonClosure VirtualRepresentation Weil.Local
open LocalWeil.Ramification

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Descend the actual continuous exact determinant through the closed
commutator quotient, then transport it by the supplied reciprocity map. -/
def fieldDeterminant (e : ReciprocityFamily F) (E : Extension F)
    (x : Virtual.{uF, uV} F E) : FieldCharacter F E := by
  letI := (fieldData F E).topology
  let δ : weilSubgroup F E →ₜ* ℂˣ :=
    ⟨ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F E) x,
      ExactGrothendieckGroup.continuous_continuousDeterminant x⟩
  exact (LocalClassField.abelianizationLiftEquiv.trans
    (LocalClassField.characterTransport (e E))) δ

@[simp]
theorem fieldDeterminant_reciprocityUnits (e : ReciprocityFamily F) (E : Extension F)
    (x : Virtual.{uF, uV} F E) (g : weilSubgroup F E) :
    fieldDeterminant F e E x (reciprocityUnits F e E g) =
      ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F E) x g := by
  let := (fieldData F E).topology
  change LocalClassField.abelianizationLift _
    ((e E).symm ((e E) (LocalClassField.abelianizationProjection _ g))) = _
  rw [(e E).symm_apply_apply]
  rfl

/-- The tensor assignment is additive in the signed high-break lattice input. -/
def tensorValueAddHom (ε : Assignment.{uF, uV} F) (hε : AdditiveRelation F ε)
    (ψ : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F))
    (w : LocalWeil.Lattice.{uF, max uF uV} F) :
    LocalWeil.Lattice.{uF, max uF uV} F →+ Additive ℂˣ :=
  (valueAddHom F ε hε _ ψ μ).comp
    (((ExactGrothendieckGroup.continuousTensorSame (realizeAtBase F w)).comp
      (realizeAtBase F)).toAddMonoidHom)

/-- The universal-lift formulation is equivalent to evaluation of the descended
field character, with exactly the same test and Haar quantifiers. -/
theorem exactWitness_iff (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F)
    (v : LocalWeil.Lattice.{uF, max uF uV} F) (a : ℝ)
    (ψ : AdditiveCharacter F (baseExtension F)) (γ : (baseExtension F).fieldˣ) :
    ExactWitness F e ε v a ψ γ ↔
      ∀ w : LocalWeil.Lattice.{uF, max uF uV} F,
        LocalWeil.degree F w = 0 → AllBreaksBelow F w (a / 2) →
        ∀ μ : HaarMeasure F (baseExtension F),
          ε _ ψ μ (ExactGrothendieckGroup.continuousTensorSame
            (realizeAtBase F w) (realizeAtBase F v)) =
            fieldDeterminant F e _ (realizeAtBase F w) γ := by
  constructor
  · intro h w hw ha μ
    obtain ⟨g, hg⟩ := reciprocityUnits_surjective F e (baseExtension F) γ
    rw [← hg, fieldDeterminant_reciprocityUnits]
    exact h w hw ha μ g hg
  · intro h w hw ha μ g hg
    rw [← fieldDeterminant_reciprocityUnits F e _ (realizeAtBase F w) g, hg]
    exact h w hw ha μ

/-- The analogous equivalence preserves the exponent's position after the
specified test and Haar measure. -/
theorem approximateWitness_iff (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F)
    (v : LocalWeil.Lattice.{uF, max uF uV} F) (a : ℝ)
    (ψ : AdditiveCharacter F (baseExtension F)) (γ : (baseExtension F).fieldˣ) :
    ApproximateWitness F e ε v a ψ γ ↔
      ∀ w : LocalWeil.Lattice.{uF, max uF uV} F,
        LocalWeil.degree F w = 0 → AllBreaksBelow F w a →
        ∀ μ : HaarMeasure F (baseExtension F), ∃ n : ℕ,
          ε _ ψ μ (ExactGrothendieckGroup.continuousTensorSame
            (realizeAtBase F w) (realizeAtBase F v)) ^ (p ^ n) =
            fieldDeterminant F e _ (realizeAtBase F w) γ ^ (p ^ n) := by
  constructor
  · intro h w hw ha μ
    obtain ⟨g, hg⟩ := reciprocityUnits_surjective F e (baseExtension F) γ
    rw [← hg, fieldDeterminant_reciprocityUnits]
    exact h w hw ha μ g hg
  · intro h w hw ha μ g hg
    rw [← fieldDeterminant_reciprocityUnits F e _ (realizeAtBase F w) g, hg]
    exact h w hw ha μ

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
