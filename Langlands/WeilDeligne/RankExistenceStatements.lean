import Langlands.WeilDeligne.Parameters

/-!
# Positive-rank Weil–Deligne parameter existence statements

These propositions use the actual pair-isomorphism quotient. They do not
assume an inhabitant or a classification, and they do not prove existence.
-/

noncomputable section

universe uG uV

namespace Langlands.WeilDeligneRepresentation.Blocks

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Honest nonemptiness of every positive-rank F-semisimple parameter class.
There is no general-linear-group representation or LLC bijection in this claim. -/
def PositiveRankParameterExistsFor (I : Subgroup G) (degree : G →* Multiplicative ℤ)
    (ν : G →* ℂˣ) : Prop :=
  ∀ n : ℕ, 0 < n →
    Nonempty (FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν) I degree n)

/-- A normalized witness: the trivial action on a rank-`n` carrier with zero
monodromy, open inertia kernel and F-semisimplicity. Every positive rank is
quantified; no nonempty parameter type is assumed as an input. -/
def TrivialRankParameterExistsFor (I : Subgroup G) (degree : G →* Multiplicative ℤ)
    (ν : G →* ℂˣ) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν,
    A.rank = n ∧ A.monodromy = 0 ∧
    IsFrobeniusSemisimpleParameter I degree A ∧
    ∀ g : G, A.representation g = 1

/-- Every positive rank has both a genuine F-semisimple parameter class
and a normalized representative with identity action and zero monodromy.
The group data are explicit; no local Weil construction is assumed here. -/
def RankParameterExistenceFor (I : Subgroup G) (degree : G →* Multiplicative ℤ)
    (ν : G →* ℂˣ) : Prop :=
  PositiveRankParameterExistsFor.{uG, uV} I degree ν ∧
    TrivialRankParameterExistsFor.{uG, uV} I degree ν

end Langlands.WeilDeligneRepresentation.Blocks
