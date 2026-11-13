import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement
import Langlands.AllField.Group.GL.BlockModulus
/-! BZ77 cuspidal embedding, finite length, association, and Hom bounds. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding CuspidalEmbeddingTheorem
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

universe uF uV uW

variable (F : Type uF) [Field F]
  (T : LocalFieldData F) (n : ℕ)

/-- Every irreducible smooth representation embeds in normalized induction
from an irreducible cuspidal representation of an actual standard Levi.
Admissibility is a conclusion, not an input. -/
def CuspidalEmbeddingTheorem : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ ω : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F),
    ω.IsIrreducible → ω.IsAdmissible ∧
    ∃ (B : BlockShape n) (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F)),
      σ.IsIrreducible ∧ IsLeviCuspidal B σ.representation ∧
      ∃ j : ω.representation.IntertwiningMap
          (Induction.smoothInduced (B.parabolic F)
            (twist (T.parabolicHalfModulus B)
              (σ.representation.comp (B.leviProjection F)))),
        Function.Injective j

end Langlands.AllField.CuspidalSupport
