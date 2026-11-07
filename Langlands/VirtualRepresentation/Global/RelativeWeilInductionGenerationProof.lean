import Langlands.VirtualRepresentation.Global.RelativeWeilInductionGenerationStatement
import Langlands.VirtualRepresentation.QuotientInducedGeneration

/-!
# Proof of Brauer induction for relative Weil groups

The projection `W_{E/F} → Gal(E/F)` has open kernel, the image of the idele
class group, which is commutative. The general theorem
`ExactGrothendieckGroup.span_quotientInducedGenerators_eq_top` therefore applies,
and its generators are exactly `inducedCharacterGenerators c F E`.
-/

noncomputable section

set_option autoImplicit false

universe u uV

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.VirtualRepresentation

variable (c : FundamentalClass.ClassFamily.{u}) (F E : Type u)
  [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

attribute [local instance] relativeGaloisTopology

/-- The kernel of the projection is the image of the idele class group, hence
commutative. -/
theorem ker_projection_comm :
    ∀ a ∈ (projection c F E).ker, ∀ b ∈ (projection c F E).ker, a * b = b * a := by
  rw [← exact c F E]
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [← map_mul, ← map_mul]
  exact congrArg (inclusion c F E) (mul_comm x y)

/-- Brauer induction for `W_{E/F}`. -/
theorem inducedCharacterGeneration : InducedCharacterGeneration.{u, uV} c F E :=
  ExactGrothendieckGroup.span_quotientInducedGenerators_eq_top.{u, u, uV}
    (projection c F E) (isOpen_ker_projection c F E) (ker_projection_comm c F E)

/-- Brauer induction for every class family and every finite Galois extension of
number fields. -/
theorem inducedCharacterGenerationStatement :
    InducedCharacterGenerationStatement.{u, uV} :=
  fun c F E _ _ _ _ _ _ => inducedCharacterGeneration c F E

end Langlands.ClassField.Global.RelativeWeilGroup
