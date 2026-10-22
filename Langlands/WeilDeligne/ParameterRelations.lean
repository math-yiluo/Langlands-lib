import Langlands.WeilDeligne.Parameters
import Langlands.WeilDeligne.Dual
import Langlands.WeilDeligne.Twist

/-!
# Dual and twist relations on Frobenius-semisimple parameter classes

The relations compare the existing underlying isomorphism classes. They do not
choose representatives or outputs, or assume preservation of parameter conditions.
-/

noncomputable section

universe uG uV

namespace Langlands.WeilDeligneRepresentation.ParameterRelations

variable {G : Type uG} [Group G] [TopologicalSpace G] {ν : G →* ℂˣ}
  {I : Subgroup G} {degree : G →* Multiplicative ℤ} {n : ℕ}

/-- Forget the rank and parameter conditions, retaining the actual pair class. -/
abbrev forget
    (D : FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν) I degree n) :
    IsomorphismClasses.{0, uG, uV} ℂ G ν :=
  frobeniusSemisimpleClassForget I degree D.val

/-- `E` is the dual of `D` when their underlying pair classes satisfy this equality.
Existence of such an `E` is a separate theorem target. -/
def IsDualOf
    (D E : FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν) I degree n) :
    Prop :=
  forget E = dualClass (forget D)

/-- `E` is the twist of `D` by `χ`, with the input before the output.
No continuity, open-kernel, closure, or totality premise is part of this definition. -/
def IsTwistOf (χ : G →* ℂˣ)
    (D E : FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν) I degree n) :
    Prop :=
  forget E = twistClass χ (forget D)

end Langlands.WeilDeligneRepresentation.ParameterRelations
