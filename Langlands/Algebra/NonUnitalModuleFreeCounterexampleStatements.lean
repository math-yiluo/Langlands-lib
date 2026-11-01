import Langlands.Algebra.CountableSupportAlgebra
import Langlands.Algebra.NonUnitalModuleFreeStatements
import Mathlib.Analysis.Complex.Cardinality

/-!
# A derived counterexample to projectivity of free nonunital modules

Renard I.5.3, printed p.27 / PDF p.33, warns of this failure without
specifying an example. These statements give the actual countable-support
example, including a complex algebra, with the original regular action.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.NonUnitalModuleFreeCounterexampleStatements

universe uR uX uL

/-- The original regular module is free, is a free summand, and is not exact-Hom projective. -/
def RegularCounterexample (R : Type uR) [CommRing R] (X : Type uX) : Prop :=
  let A := CountableSupportAlgebra.Carrier R X
  let hA : IsIdempotented A := CountableSupportAlgebra.isIdempotented
  letI := NondegenerateModuleCat.abelian.{max uR uX, max (max uR uX) uL} A hA
  let P := NonUnitalModuleFree.regularObject.{max uR uX, uL} hA
  NonUnitalModuleFree.IsFree.{max uR uX, uL} hA P ∧
    ¬ Langlands.Renard.HomProjective P ∧
    ∃ (I : Type (max (max uR uX) uL))
      (Q : NondegenerateModuleCat.{max uR uX, max (max uR uX) uL} A),
      Nonempty (NonUnitalModuleFree.object.{max uR uX, uL, max (max uR uX) uL} hA I ≅ P ⊞ Q)

/-- The construction gives a counterexample for every nontrivial coefficient ring and uncountable base. -/
def GeneralCounterexamplesStatement : Prop :=
  ∀ (R : Type uR) [CommRing R] [Nontrivial R] (X : Type uX) [Uncountable X],
    RegularCounterexample.{uR, uX, uL} R X

/-- The actual algebra of countably supported complex functions on the complex numbers is a counterexample. -/
def ComplexCounterexampleStatement : Prop :=
  RegularCounterexample.{0, 0, uL} ℂ ℂ

/-- The general construction and its explicit complex instance. -/
def FreeCounterexampleAssertions : Prop :=
  GeneralCounterexamplesStatement.{uR, uX, uL} ∧ ComplexCounterexampleStatement.{uL}

/-! Coefficient, base-set and regular-lift universes remain independent. -/

example : Prop := GeneralCounterexamplesStatement.{uR, uX, uL}
example : Prop := GeneralCounterexamplesStatement.{0, 1, 2}
example : Prop := GeneralCounterexamplesStatement.{0, 2, 1}
example : Prop := GeneralCounterexamplesStatement.{1, 0, 2}
example : Prop := GeneralCounterexamplesStatement.{1, 2, 0}
example : Prop := GeneralCounterexamplesStatement.{2, 0, 1}
example : Prop := GeneralCounterexamplesStatement.{2, 1, 0}
example : Prop := ComplexCounterexampleStatement.{uL}

end Langlands.Algebra.NonUnitalModuleFreeCounterexampleStatements
