import Langlands.WeilDeligne.ParameterRelations

/-!
# Existence and uniqueness targets for parameter-class operations

These are proposition definitions, not proofs. No preservation theorem is an
assumption, and no output is selected in the underlying relation definitions.
-/

noncomputable section

universe uG uV

namespace Langlands.WeilDeligneRepresentation.ParameterRelationLaws

open ParameterRelations

variable {G : Type uG} [Group G] [TopologicalSpace G] {ν : G →* ℂˣ}

/-- Forgetting the predicates and rank does not identify distinct restricted classes. -/
def ForgetInjective : Prop :=
  ∀ (I : Subgroup G) (degree : G →* Multiplicative ℤ) (n : ℕ),
    Function.Injective
      (ParameterRelations.forget : FrobeniusSemisimpleParameterClassesOfRank.{uG, uV}
        (ν := ν) I degree n → IsomorphismClasses.{0, uG, uV} ℂ G ν)

/-- The relations assert actual pair isomorphisms between any representatives. -/
def RepresentativeCharacterizations : Prop :=
  ∀ (I : Subgroup G) (degree : G →* Multiplicative ℤ) (n : ℕ)
    (D E : FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν) I degree n)
    (A B : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν),
    ParameterRelations.forget D = classOf A → ParameterRelations.forget E = classOf B →
    (IsDualOf D E ↔ Nonempty (Equiv B (dual A))) ∧
    ∀ χ : G →* ℂˣ, (IsTwistOf χ D E ↔ Nonempty (Equiv B (twist χ A)))

/-- Rank preservation on all pair classes, before any parameter conditions. -/
def ClassRankPreservation : Prop :=
  ∀ c : IsomorphismClasses.{0, uG, uV} ℂ G ν,
    classRank (dualClass c) = classRank c ∧
    ∀ χ : G →* ℂˣ, classRank (twistClass χ c) = classRank c

/-- The rank-indexed inputs and the unrestricted operation outputs have rank `n`. -/
def RankNormalization : Prop :=
  ∀ (I : Subgroup G) (degree : G →* Multiplicative ℤ) (n : ℕ)
    (D : FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν) I degree n),
    classRank (ParameterRelations.forget D) = n ∧
    classRank (dualClass (ParameterRelations.forget D)) = n ∧
    ∀ χ : G →* ℂˣ, classRank (twistClass χ (ParameterRelations.forget D)) = n

/-- Each dual relation has at most one restricted output. -/
def DualUniqueness : Prop :=
  ∀ (I : Subgroup G) (degree : G →* Multiplicative ℤ) (n : ℕ)
    (D E F : FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν) I degree n),
    IsDualOf D E → IsDualOf D F → E = F

/-- Each twist relation has at most one restricted output, even without a closure premise. -/
def TwistUniqueness : Prop :=
  ∀ (I : Subgroup G) (degree : G →* Multiplicative ℤ) (n : ℕ) (χ : G →* ℂˣ)
    (D E F : FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν) I degree n),
    IsTwistOf χ D E → IsTwistOf χ D F → E = F

/-- The actual dual preserves both parameter conditions and rank. -/
def DualPreservation : Prop :=
  ∀ (I : Subgroup G) (degree : G →* Multiplicative ℤ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν),
    IsFrobeniusSemisimpleParameter I degree A →
    IsFrobeniusSemisimpleParameter I degree (dual A) ∧ (dual A).rank = A.rank

/-- Duality has an output in the same rank-indexed parameter set. -/
def DualExistence : Prop :=
  ∀ (I : Subgroup G) (degree : G →* Multiplicative ℤ) (n : ℕ)
    (D : FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν) I degree n),
    ∃ E, IsDualOf D E

/-- The unique dual output is asserted existentially, with no selected dual function. -/
def DualUniqueExistence : Prop :=
  ∀ (I : Subgroup G) (degree : G →* Multiplicative ℤ) (n : ℕ)
    (D : FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν) I degree n),
    ∃! E, IsDualOf D E

/-- Biduality and the trivial/inverse character laws as relations on existing outputs. -/
def InverseLaws : Prop :=
  ∀ (I : Subgroup G) (degree : G →* Multiplicative ℤ) (n : ℕ)
    (D E : FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν) I degree n),
    (IsDualOf D E ↔ IsDualOf E D) ∧
    (IsTwistOf 1 D E ↔ E = D) ∧
    ∀ χ : G →* ℂˣ, (IsTwistOf χ D E ↔ IsTwistOf χ⁻¹ E D)

/-- Successive character twists multiply, with the second twist on the left. -/
def TwistComposition : Prop :=
  ∀ (I : Subgroup G) (degree : G →* Multiplicative ℤ) (n : ℕ) (χ ψ : G →* ℂˣ)
    (D E F : FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν) I degree n),
    IsTwistOf χ D E → IsTwistOf ψ E F → IsTwistOf (ψ * χ) D F

/-- Duality inverts the twisting character. -/
def DualTwistCompatibility : Prop :=
  ∀ (I : Subgroup G) (degree : G →* Multiplicative ℤ) (n : ℕ) (χ : G →* ℂˣ)
    (D E D' E' :
      FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν) I degree n),
    IsTwistOf χ D E → IsDualOf D D' → IsDualOf E E' → IsTwistOf χ⁻¹ D' E'

/-- All targets which need no compatibility axiom between the topology and group. -/
def AlgebraicFamily : Prop :=
  ForgetInjective.{uG, uV} (ν := ν) ∧
  RepresentativeCharacterizations.{uG, uV} (ν := ν) ∧
  ClassRankPreservation.{uG, uV} (ν := ν) ∧
  RankNormalization.{uG, uV} (ν := ν) ∧
  DualUniqueness.{uG, uV} (ν := ν) ∧
  TwistUniqueness.{uG, uV} (ν := ν) ∧
  DualPreservation.{uG, uV} (ν := ν) ∧
  DualExistence.{uG, uV} (ν := ν) ∧
  DualUniqueExistence.{uG, uV} (ν := ν) ∧
  InverseLaws.{uG, uV} (ν := ν) ∧
  TwistComposition.{uG, uV} (ν := ν) ∧
  DualTwistCompatibility.{uG, uV} (ν := ν)

/-- An open inertia kernel for the character gives preservation of the actual objects.
Usual complex continuity is a distinct condition and is not required here.
The topological-group structure is an explicit binder, so it stays in the type. -/
def TwistPreservation [IsTopologicalGroup G] : Prop :=
  ∀ (I : Subgroup G) (degree : G →* Multiplicative ℤ) (χ : G →* ℂˣ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν),
    IsOpen ((χ.comp I.subtype).ker : Set I) →
    IsFrobeniusSemisimpleParameter I degree A →
    IsFrobeniusSemisimpleParameter I degree (twist χ A) ∧ (twist χ A).rank = A.rank

/-- Twist existence under the character's open-inertia-kernel hypothesis. -/
def TwistExistence [IsTopologicalGroup G] : Prop :=
  ∀ (I : Subgroup G) (degree : G →* Multiplicative ℤ) (n : ℕ) (χ : G →* ℂˣ),
    IsOpen ((χ.comp I.subtype).ker : Set I) →
    ∀ D : FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν) I degree n,
      ∃ E, IsTwistOf χ D E

/-- The unique twist output is existential, with precisely the same closure premise. -/
def TwistUniqueExistence [IsTopologicalGroup G] : Prop :=
  ∀ (I : Subgroup G) (degree : G →* Multiplicative ℤ) (n : ℕ) (χ : G →* ℂˣ),
    IsOpen ((χ.comp I.subtype).ker : Set I) →
    ∀ D : FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν) I degree n,
      ∃! E, IsTwistOf χ D E

/-- Complete class-relation target; no clause is assumed in another clause's premises. -/
def Statement [IsTopologicalGroup G] : Prop :=
  AlgebraicFamily.{uG, uV} (ν := ν) ∧
  TwistPreservation.{uG, uV} (ν := ν) ∧
  TwistExistence.{uG, uV} (ν := ν) ∧
  TwistUniqueExistence.{uG, uV} (ν := ν)

end Langlands.WeilDeligneRepresentation.ParameterRelationLaws
