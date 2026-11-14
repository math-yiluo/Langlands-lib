import Langlands.AllFieldBZ.Representation.Induction.Parabolic
import Langlands.Representation.Induction.Equivalences

/-!
# All-field port of `Langlands.Representation.Induction.Equivalences`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Induction.Equivalences` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Induction
open Langlands.Induction
universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

end Langlands.AllFieldBZ.Induction
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uF uV uW

variable {F : LocalFieldPackage.{uF}}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- An injective Levi map remains injective after normalized parabolic induction. -/
theorem normalizedParabolicInducedMap_injective
    {σ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W}
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
    {σ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W}
    (e : σ.Equiv τ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedParabolicInduced B σ).Equiv (T.normalizedParabolicInduced B τ) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  Induction.smoothInducedEquiv (B.parabolic F.Carrier)
    (twistEquiv (T.parabolicHalfModulus B)
      (Representation.Equiv.mk e.toLinearEquiv
        (fun g => e.isIntertwining' (B.leviProjection F.Carrier g))))

@[simp]
theorem normalizedParabolicInducedEquiv_eval
    {σ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W}
    (e : σ.Equiv τ)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))))
    (g : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval _ _ (T.normalizedParabolicInducedEquiv B e f) g =
      e (Induction.eval _ _ f g) := rfl

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
