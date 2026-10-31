import Langlands.Algebra.IntegerUnitizationCategory
import Langlands.Algebra.IntegerOriginalSubmoduleGenerationStatements
import Langlands.CategoryTheory.RenardFiniteType

/-!
# Object finiteness for original additive nonunital modules

Internal comparison statements motivated by Renard's Chapter I module
conventions and Appendix A.I.2–A.I.3. These targets use the actual
`NonUnitalModuleCat`, its stored original action and the canonical integer
unitization. They supply no proofs or source convention for nonunital
Noetherian algebras.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleFiniteness

universe uA uM

/-- Source categorical finite type agrees with finite generation for the
canonical integer-unitized action on the same carrier. -/
def FiniteTypeStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (M : NonUnitalModuleCat.{uA, uM} A),
    Langlands.Renard.IsFiniteTypeObject M ↔
      (letI := CompatibleUnitization.module
        (NonUnitalModule.toIntLinearEndHom (A := A) (V := M));
        Module.Finite (Unitization ℤ A) M)

/-- Source finite subcovers agree with finite generation for that exact
canonical integer-unitized action. -/
def FiniteSubcoverStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (M : NonUnitalModuleCat.{uA, uM} A),
    Langlands.Renard.HasFiniteSubcoverProperty M ↔
      (letI := CompatibleUnitization.module
        (NonUnitalModule.toIntLinearEndHom (A := A) (V := M));
        Module.Finite (Unitization ℤ A) M)

/-- Source categorical Noetherianity agrees with algebraic Noetherianity
for that exact canonical integer-unitized action. -/
def NoetherianStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (M : NonUnitalModuleCat.{uA, uM} A),
    Langlands.Renard.IsNoetherianObject M ↔
      (letI := CompatibleUnitization.module
        (NonUnitalModule.toIntLinearEndHom (A := A) (V := M));
        IsNoetherian (Unitization ℤ A) M)

/-- Source categorical finite type is the finite-generator universal
property among the original stable additive subgroups. -/
def FiniteGenerationStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (M : NonUnitalModuleCat.{uA, uM} A),
    Langlands.Renard.IsFiniteTypeObject M ↔
      ∃ S : Finset M, ∀ P : NonUnitalSubmodule A M,
        (↑S : Set M) ⊆ P → ∀ m : M, m ∈ P

/-- Source categorical Noetherianity is finite stable generation of every
original stable additive subgroup. -/
def NoetherianGenerationStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (M : NonUnitalModuleCat.{uA, uM} A),
    Langlands.Renard.IsNoetherianObject M ↔
      ∀ P : NonUnitalSubmodule A M,
        ∃ S : Finset M, (↑S : Set M) ⊆ P ∧
          ∀ Q : NonUnitalSubmodule A M, (↑S : Set M) ⊆ Q → P ≤ Q

/-- The finite-type, finite-subcover, Noetherian, whole-module generation
and all-subgroups generation comparisons, in that order. -/
def NonUnitalModuleFinitenessStatement : Prop :=
  FiniteTypeStatement.{uA, uM} ∧
    FiniteSubcoverStatement.{uA, uM} ∧
    NoetherianStatement.{uA, uM} ∧
    FiniteGenerationStatement.{uA, uM} ∧
    NoetherianGenerationStatement.{uA, uM}

end Langlands.Algebra.NonUnitalModuleFiniteness
