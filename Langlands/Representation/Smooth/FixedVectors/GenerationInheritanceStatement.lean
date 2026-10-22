import Langlands.Representation.Smooth.Definitions
import Langlands.Representation.Category.Subquotients
import Mathlib.RepresentationTheory.Semisimple

/-!
# Inheritance of semisimple fixed-vector generation

Proposition targets for Worker 196's algebraic inheritance interface.
The same subgroup is retained under surjections, injections into a semisimple
representation, and actual smooth subquotients after restriction.
-/

namespace Langlands

/-- Semisimplicity and generation by `K`-fixed vectors pass through a
surjective intertwiner, without assuming surjectivity on fixed vectors. -/
def SemisimpleFixedVectorsGenerateOfSurjectiveStatement.{uR, uG, uV, uW} : Prop :=
  ∀ (R : Type uR) [Field R] (G : Type uG) [Group G]
    (V : Type uV) [AddCommGroup V] [Module R V]
    (W : Type uW) [AddCommGroup W] [Module R W]
    (ρ : Representation R G V) (σ : Representation R G W)
    (K : Subgroup G) (f : ρ.IntertwiningMap σ),
    Function.Surjective f →
    Representation.IsSemisimpleRepresentation ρ →
    (∀ S : Subrepresentation ρ, fixedVectors ρ K ≤ S.toSubmodule → S = ⊤) →
    Representation.IsSemisimpleRepresentation σ ∧
      ∀ S : Subrepresentation σ, fixedVectors σ K ≤ S.toSubmodule → S = ⊤

/-- Semisimplicity and generation by `K`-fixed vectors pass to the source of
an injective intertwiner into a semisimple representation. -/
def SemisimpleFixedVectorsGenerateOfInjectiveStatement.{uR, uG, uV, uW} : Prop :=
  ∀ (R : Type uR) [Field R] (G : Type uG) [Group G]
    (V : Type uV) [AddCommGroup V] [Module R V]
    (W : Type uW) [AddCommGroup W] [Module R W]
    (ρ : Representation R G V) (σ : Representation R G W)
    (K : Subgroup G) (f : ρ.IntertwiningMap σ),
    Function.Injective f →
    Representation.IsSemisimpleRepresentation σ →
    (∀ S : Subrepresentation σ, fixedVectors σ K ≤ S.toSubmodule → S = ⊤) →
    Representation.IsSemisimpleRepresentation ρ ∧
      ∀ S : Subrepresentation ρ, fixedVectors ρ K ≤ S.toSubmodule → S = ⊤

namespace SmoothRep

/-- Semisimplicity over `H` and generation over `H` by ambient `K`-fixed
vectors pass to actual smooth subquotients when `K ≤ H`. -/
def SemisimpleFixedVectorsGenerateSubquotientStatement.{uR, uG, uV} : Prop :=
  ∀ (R : Type uR) [Field R] (G : Type uG) [Group G] [TopologicalSpace G]
    (A B : SmoothRep.{uR, uG, uV} R G) (H K : Subgroup G),
    K ≤ H →
    Representation.IsSemisimpleRepresentation (A.representation.comp H.subtype) →
    (∀ S : Subrepresentation (A.representation.comp H.subtype),
      fixedVectors A.representation K ≤ S.toSubmodule → S = ⊤) →
    IsSubquotient B A →
    Representation.IsSemisimpleRepresentation (B.representation.comp H.subtype) ∧
      ∀ S : Subrepresentation (B.representation.comp H.subtype),
        fixedVectors B.representation K ≤ S.toSubmodule → S = ⊤

end SmoothRep

/-- All three inheritance statements, with independent coefficient, group,
source-carrier and target-carrier universes. -/
def SemisimpleFixedVectorsGenerationInheritanceStatement.{uR, uG, uV, uW} : Prop :=
  SemisimpleFixedVectorsGenerateOfSurjectiveStatement.{uR, uG, uV, uW} ∧
  SemisimpleFixedVectorsGenerateOfInjectiveStatement.{uR, uG, uV, uW} ∧
  SmoothRep.SemisimpleFixedVectorsGenerateSubquotientStatement.{uR, uG, uV}

end Langlands
