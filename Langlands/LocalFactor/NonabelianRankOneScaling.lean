import Langlands.LocalFactor.Abelian.Scaling
import Langlands.LocalFactor.NonabelianScalingStatement

/-! Rank-one evaluation of the fixed-Haar scaling law in the actual exact group. -/

noncomputable section

universe uG uV uF

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

@[simp]
theorem determinantCharacter_characterLine (χ : G →* ℂˣ) :
    determinantCharacter (characterLine.{uG, uV} χ) = χ := by
  ext w
  change LinearMap.det ((χ w : ℂ) • (1 : Module.End ℂ (ULift.{uV} ℂ))) = (χ w : ℂ)
  simp

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

variable {G : Type uG} [Group G] [TopologicalSpace G]

@[simp]
theorem determinantCharacter_characterClass (χ : G →ₜ* ℂˣ) :
    determinantCharacter (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)
      (characterClass.{uG, uV} χ) = χ.toMonoidHom := by
  rw [characterClass, determinantCharacter_ofRepresentation,
    FiniteRepresentation.determinantCharacter_characterLine]

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.LocalFactor.CommonClosure

open VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

@[simp]
theorem determinantCharacter_characterClass (e : ReciprocityFamily F)
    (E : Extension F) (χ : FieldCharacter F E) :
    ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F E)
      (characterClass.{uF, uV} F e E χ) = (weilCharacter F e E χ).toMonoidHom :=
  ExactGrothendieckGroup.determinantCharacter_characterClass _

end Langlands.LocalFactor.CommonClosure

namespace Langlands.LocalFactor.NonabelianSystem

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

theorem additiveCharacterScaling_characterClass
    {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hε : RankOneRelation F e ε) (E : Extension F) (χ : FieldCharacter F E) :
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    ∀ (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
      (a : E.fieldˣ) (w : weilSubgroup F E),
      reciprocityUnits F e E w = a →
      (ε E (ψ.scale a) μ (characterClass F e E χ) : ℂ) =
        (ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F E)
            (characterClass F e E χ) w : ℂ) *
          ((fieldData F E).normalizedAbs (a : E.field) : ℂ) ^
            (-degree F E (characterClass F e E χ)) *
          (ε E ψ μ (characterClass F e E χ) : ℂ) := by
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  intro ψ μ a w ha
  rw [hε E χ (ψ.scale a) μ, hε E χ ψ μ,
    (fieldData F E).abelianEpsilonExpression_scale,
    CommonClosure.determinantCharacter_characterClass,
    CommonClosure.degree_characterClass]
  change (χ a : ℂ) * _ * _ =
    (χ (reciprocityUnits F e E w) : ℂ) * _ ^ (-1 : ℤ) * _
  simp only [ha, zpow_neg_one]

end Langlands.LocalFactor.NonabelianSystem
