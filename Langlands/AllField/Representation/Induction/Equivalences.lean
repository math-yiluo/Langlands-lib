import Langlands.Representation.Induction.Equivalences
import Langlands.AllField.Representation.Induction.Parabolic
/-!
# Transport of smooth induction along representation equivalences

Postcomposition by an equivalence transports smooth induced functions, including
between independent carrier universes. Normalized parabolic induction specializes
this construction after inflation and the common character twist.
-/

noncomputable section

namespace Langlands.AllField.Induction
open Langlands.Induction
open Langlands.AllField.Induction

universe uR uG uV uW


end Langlands.AllField.Induction

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF uV uW

variable {F : Type uF} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- An injective Levi map remains injective after normalized parabolic induction. -/
theorem normalizedParabolicInducedMap_injective
    {σ : Representation ℂ (B.Levi F) V}
    {τ : Representation ℂ (B.Levi F) W}
    (f : σ.IntertwiningMap τ) (hf : Function.Injective f) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Function.Injective (T.normalizedParabolicInducedMap B f) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  funext g
  apply hf
  exact congrArg (fun z => z.1.1 g) h

/-- Normalize, inflate, and induce an actual Levi equivalence. The two Levi
representation carriers may lie in independent universes. -/
def normalizedParabolicInducedEquiv
    {σ : Representation ℂ (B.Levi F) V}
    {τ : Representation ℂ (B.Levi F) W}
    (e : σ.Equiv τ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedParabolicInduced B σ).Equiv (T.normalizedParabolicInduced B τ) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  Induction.smoothInducedEquiv (B.parabolic F)
    (twistEquiv (T.parabolicHalfModulus B)
      (Representation.Equiv.mk e.toLinearEquiv
        (fun g => e.isIntertwining' (B.leviProjection F g))))

@[simp]
theorem normalizedParabolicInducedEquiv_eval
    {σ : Representation ℂ (B.Levi F) V}
    {τ : Representation ℂ (B.Levi F) W}
    (e : σ.Equiv τ)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F))))
    (g : GeneralLinear n F) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval _ _ (T.normalizedParabolicInducedEquiv B e f) g =
      e (Induction.eval _ _ f g) := rfl

end Langlands.LocalFieldData
