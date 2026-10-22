import Langlands.VirtualRepresentation.ExactTwist
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Character lines in arbitrary carrier universes

The action is scalar multiplication on a lifted copy of the coefficient field.
The lift permits use in the existing exact virtual group without fixing its
carrier universe to zero.
-/

noncomputable section

universe uG uV

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

/-- The actual scalar character representation on a universe-lifted complex line. -/
def characterLine (χ : G →* ℂˣ) : FiniteRepresentation.{0, uG, uV} ℂ G :=
  of (Langlands.twist χ (Representation.trivial ℂ G (ULift.{uV} ℂ)))

@[simp]
theorem characterLine_apply (χ : G →* ℂˣ) (g : G) (v : ULift.{uV} ℂ) :
    (characterLine.{uG, uV} χ).representation g v = (χ g : ℂ) • v := rfl

/-- The lift is an actual intertwining equivalence to the existing scalar model. -/
def characterLineEquiv (χ : G →* ℂˣ) :
    Equiv (characterLine.{uG, uV} χ) (of (Langlands.characterRepresentation χ)) where
  toLinearEquiv := ULift.moduleEquiv
  isIntertwining' g := by
    ext v
    rfl

@[simp]
theorem characterLine_rank (χ : G →* ℂˣ) :
    (characterLine.{uG, uV} χ).rank = 1 := by
  exact (rank_eq_of_equiv (characterLineEquiv.{uG, uV} χ)).trans
    (Module.finrank_self ℂ)

/-- Scalar twisting multiplies the character on the same actual line. -/
def twistCharacterLineEquiv (χ η : G →* ℂˣ) :
    Equiv (twist χ (characterLine.{uG, uV} η)) (characterLine.{uG, uV} (χ * η)) := by
  change (Langlands.twist χ
    (Langlands.twist η (Representation.trivial ℂ G (ULift.{uV} ℂ)))).Equiv
      (Langlands.twist (χ * η) (Representation.trivial ℂ G (ULift.{uV} ℂ)))
  rw [Langlands.twist_twist]
  exact Representation.Equiv.refl _

variable [TopologicalSpace G]

/-- A continuous character gives continuity in the usual endomorphism topology. -/
theorem characterLine_isContinuous (χ : G →ₜ* ℂˣ) :
    (characterLine.{uG, uV} χ.toMonoidHom).IsContinuous := by
  let : TopologicalSpace (Module.End ℂ (ULift.{uV} ℂ)) :=
    moduleTopology ℂ (Module.End ℂ (ULift.{uV} ℂ))
  have hc : Continuous (fun z : ℂ => z • (1 : Module.End ℂ (ULift.{uV} ℂ))) :=
    continuous_id.smul continuous_const
  exact hc.comp (Units.continuous_val.comp χ.continuous)

/-- The same line with its proved continuity certificate. -/
def continuousCharacterLine (χ : G →ₜ* ℂˣ) : ContinuousObjects.{uG, uV} G :=
  ⟨characterLine χ.toMonoidHom, characterLine_isContinuous χ⟩

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The genuine exact virtual class of a continuous character line. -/
def characterClass (χ : G →ₜ* ℂˣ) :
    ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) :=
  ofRepresentation _ ⟨FiniteRepresentation.characterLine χ.toMonoidHom,
    FiniteRepresentation.characterLine_isContinuous χ⟩

@[simp]
theorem degree_characterClass (χ : G →ₜ* ℂˣ) :
    degree (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)
      (characterClass.{uG, uV} χ) = 1 := by
  rw [characterClass, degree_ofRepresentation]
  simp

/-- Character multiplication is compatible with the constructed virtual twist. -/
theorem continuousTwist_characterClass (χ η : G →ₜ* ℂˣ) :
    continuousTwist.{uG, uV} χ (characterClass.{uG, uV} η) =
      characterClass.{uG, uV} (χ * η) := by
  change twist χ.toMonoidHom _ _ _ (ofRepresentation _
    ⟨FiniteRepresentation.characterLine η.toMonoidHom,
      FiniteRepresentation.characterLine_isContinuous η⟩) = _
  rw [twist_ofRepresentation]
  exact ofRepresentation_eq_of_equiv _
    (FiniteRepresentation.twistCharacterLineEquiv χ.toMonoidHom η.toMonoidHom)

end Langlands.VirtualRepresentation.ExactGrothendieckGroup
