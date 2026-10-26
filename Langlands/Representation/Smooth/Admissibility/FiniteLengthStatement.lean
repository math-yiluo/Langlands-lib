import Langlands.LocalField.Definitions
import Langlands.Representation.Smooth.FiniteLengthGrothendieck

/-!
# Admissibility of finite-length smooth GL and product-Levi representations

Proposition definitions only. The field topology is the one recorded in the
supplied `T`; the carrier universe `uV` is independent of the field universe
`uF`.
-/

namespace Langlands

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every complex smooth representation of the actual `GL_n(F)` of finite
group-algebra length is admissible, for every rank `n`, including `n = 0`. -/
def GLFiniteLengthAdmissibilityStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)),
    A.HasFiniteLength → A.IsAdmissible

/-- Every complex smooth representation of finite group-algebra length of an
actual product Levi `B.Levi F`, with its product topology, is admissible,
including empty block shapes. -/
def LeviFiniteLengthAdmissibilityStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape n) (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    A.HasFiniteLength → A.IsAdmissible

/-- The combined target: both clauses, at the same field data and the same
independent universes. -/
def FiniteLengthAdmissibilityStatement : Prop :=
  GLFiniteLengthAdmissibilityStatement.{uF, uV} F T ∧
    LeviFiniteLengthAdmissibilityStatement.{uF, uV} F T

/-! ### Universe accounting

The saturated substitution `uV := max uF uV` gives exactly the carrier universe
of `GeneralLinear.FiniteLengthGrothendieckGroup` and
`BlockShape.FiniteLengthGrothendieckGroup`. -/

example (n : ℕ) (B : BlockShape n) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier =
        SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ
          (GeneralLinear n F.Carrier) ∧
      B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier =
        SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ (B.Levi F.Carrier) :=
  ⟨rfl, rfl⟩

/-- At `uV := max uF uV`, the combined target applies to every object of the
finite-length categories whose classes generate the two saturated groups. -/
example (h : FiniteLengthAdmissibilityStatement.{uF, max uF uV} F T) (n : ℕ)
    (B : BlockShape n) :
    letI := T.topology
    (∀ A : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
        A.val.IsAdmissible) ∧
      ∀ A : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (B.Levi F.Carrier),
        A.val.IsAdmissible :=
  ⟨fun A => h.1 n A.val A.property, fun A => h.2 n B A.val A.property⟩

/-- The same clauses apply to the exact inputs of the two saturated class maps. -/
example (h : FiniteLengthAdmissibilityStatement.{uF, max uF uV} F T) (n : ℕ)
    (B : BlockShape n) :
    letI := T.topology
    (∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
        (hA : A.HasFiniteLength),
        GeneralLinear.finiteLengthClass.{uV, uF} n F.Carrier A hA =
            SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A hA ∧
          A.IsAdmissible) ∧
      ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)) (hA : A.HasFiniteLength),
        B.finiteLengthClass.{uV, uF} F.Carrier A hA =
            SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A hA ∧
          A.IsAdmissible :=
  ⟨fun A hA => ⟨rfl, h.1 n A hA⟩, fun A hA => ⟨rfl, h.2 n B A hA⟩⟩

end Langlands
