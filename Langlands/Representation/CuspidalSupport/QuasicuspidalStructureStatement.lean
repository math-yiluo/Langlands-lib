import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Smooth.Contragredient.Definitions
import Langlands.Group.GL.PadicBlocks

/-! The quasicuspidal structure prerequisites of BZ77 section 2.4. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- Every actual smooth subquotient of a quasicuspidal representation is
quasicuspidal. No admissibility or finite-length hypothesis is imposed. -/
def LeviQuasicuspidalSubquotientTheorem : Prop :=
  letI := T.topology
  ∀ A D : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
    IsLeviQuasicuspidal B A.representation → SmoothRep.IsSubquotient D A →
      IsLeviQuasicuspidal B D.representation

/-- A smooth representation splits into complementary actual invariant
subspaces, one quasicuspidal and the other with no nonzero quasicuspidal
subquotient. `IsCompl` asserts both zero intersection and full sum. -/
def LeviQuasicuspidalDecompositionTheorem : Prop :=
  letI := T.topology
  ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
    ∃ S Q : Subrepresentation A.representation,
      IsCompl S.toSubmodule Q.toSubmodule ∧
      IsLeviQuasicuspidal B (SmoothRep.subrepresentation A S).representation ∧
      ∀ D : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
        SmoothRep.IsSubquotient D (SmoothRep.subrepresentation A Q) →
        IsLeviQuasicuspidal B D.representation → Subsingleton D

/-- An irreducible cuspidal constituent of an admissible representation
occurs both as an actual subrepresentation and as an actual quotient. -/
def LeviCuspidalConstituentTheorem : Prop :=
  letI := T.topology
  ∀ A D : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
    A.IsAdmissible → D.IsIrreducible → IsLeviCuspidal B D.representation →
    SmoothRep.IsSubquotient D A →
      SmoothRep.IsSubrepresentation D A ∧ SmoothRep.IsQuotient D A

/-- The smooth contragredient of an admissible quasicuspidal representation
is again admissible and quasicuspidal. Irreducibility is not required. -/
def LeviCuspidalContragredientTheorem : Prop :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
    IsLeviCuspidal B A.representation →
      IsLeviCuspidal B (smoothContragredient A.representation)

/-- BZ77's section 2.4 subquotient observation and parts (a)-(c),
specialized to all positive-rank product Levis over actual p-adic fields.
The proper-induction clause (d) belongs to the normalized induction family. -/
def PadicLeviQuasicuspidalStructureTheorems : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n → ∀ B : BlockShape n,
      LeviQuasicuspidalSubquotientTheorem.{uF, uV} F T B ∧
      LeviQuasicuspidalDecompositionTheorem.{uF, uV} F T B ∧
      LeviCuspidalConstituentTheorem.{uF, uV} F T B ∧
      LeviCuspidalContragredientTheorem.{uF, uV} F T B

end Langlands.CuspidalSupport
