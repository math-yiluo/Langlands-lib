import Langlands.Automorphic.RegularAlgebraic

/-!
# Regular highest weight at infinity

The infinitesimal character of an irreducible algebraic representation of
`∏_σ GL_n(ℂ)` whose highest weight is regular: strictly decreasing at every
embedding index. In terms of the Langlands parameters at a complex place, the
weights `μ_i + (n + 1)/2 − i` are then at distance at least `2` from one another.
This strengthens the regular infinitesimal character of Henniart 2001, §5.5, and
Clozel's regular algebraic type of `Langlands.Automorphic.RegularAlgebraic`, which
asks only for a dominant (nonincreasing) highest weight.
-/

noncomputable section

universe u

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- `χ` is the infinitesimal character of an irreducible algebraic representation of
`∏_σ GL_n(ℂ)` whose highest weight is regular: an integral weight that is strictly
decreasing at every embedding index. -/
def IsRegularHighestWeightCharacter (χ : EnvelopingCenter K n →ₐ[ℂ] ℂ) : Prop :=
  ∃ μ : EmbeddingIndex K → Fin n → ℤ,
    (∀ j, StrictAnti (μ j)) ∧ IsHighestWeightCharacter K n (fun j i => (μ j i : ℂ)) χ

variable {K n}

/-- A regular highest weight is dominant, so its infinitesimal character is regular
algebraic. -/
theorem IsRegularHighestWeightCharacter.isRegularAlgebraicCharacter
    {χ : EnvelopingCenter K n →ₐ[ℂ] ℂ} (h : IsRegularHighestWeightCharacter K n χ) :
    IsRegularAlgebraicCharacter K n χ := by
  obtain ⟨μ, hμ, hχ⟩ := h
  exact ⟨μ, fun j => (hμ j).antitone, hχ⟩

end Langlands.Global.ArchimedeanGL

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

namespace OperatorRealization

variable (S T : OperatorRealization F n)

/-- The realization has the infinitesimal character of an irreducible algebraic
representation with regular highest weight. -/
def HasRegularHighestWeight : Prop :=
  ∃ χ : ArchimedeanGL.EnvelopingCenter F n →ₐ[ℂ] ℂ,
    ArchimedeanGL.IsRegularHighestWeightCharacter F n χ ∧ S.HasInfinitesimalCharacter χ

variable {S T}

/-- Regular highest weight implies Clozel's regular algebraic type. -/
theorem HasRegularHighestWeight.isRegularAlgebraic (h : S.HasRegularHighestWeight) :
    S.IsRegularAlgebraic := by
  obtain ⟨χ, hχ, hS⟩ := h
  exact ⟨χ, hχ.isRegularAlgebraicCharacter, hS⟩

/-- Regular highest weight is invariant under full-operator equivalence. -/
theorem hasRegularHighestWeight_iff_of_equivalence (e : S.Equivalence T) :
    S.HasRegularHighestWeight ↔ T.HasRegularHighestWeight := by
  simp only [HasRegularHighestWeight, hasInfinitesimalCharacter_iff_of_equivalence e]

/-- A full-operator class has regular highest weight when some representative has. -/
def IsoClass.HasRegularHighestWeight (c : IsoClass F n) : Prop :=
  ∃ S : OperatorRealization F n, S.isoClass = c ∧ S.HasRegularHighestWeight

/-- For a class, one representative has regular highest weight exactly when every
representative has. -/
theorem isoClass_hasRegularHighestWeight_iff (S : OperatorRealization F n) :
    S.isoClass.HasRegularHighestWeight ↔ S.HasRegularHighestWeight := by
  constructor
  · rintro ⟨T, hT, hTS⟩
    obtain ⟨e⟩ := (T.isoClass_eq_iff S).mp hT
    exact (hasRegularHighestWeight_iff_of_equivalence e).mp hTS
  · intro h
    exact ⟨S, rfl, h⟩

/-- A class with regular highest weight has regular algebraic type. -/
theorem IsoClass.HasRegularHighestWeight.isRegularAlgebraic {c : IsoClass F n}
    (h : c.HasRegularHighestWeight) : c.IsRegularAlgebraic := by
  obtain ⟨S, hS, hR⟩ := h
  exact ⟨S, hS, hR.isRegularAlgebraic⟩

end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- An irreducible cuspidal class has regular highest weight at infinity when its
full-operator class has: its infinitesimal character is that of an irreducible
algebraic representation whose highest weight is strictly decreasing at every
embedding index. -/
def IsoClass.HasRegularHighestWeight (c : IsoClass F r) : Prop :=
  c.toOperatorClass.HasRegularHighestWeight

theorem isoClass_hasRegularHighestWeight_iff (S : CuspidalOperatorRealization F r) :
    S.isoClass.HasRegularHighestWeight ↔ S.realization.HasRegularHighestWeight :=
  S.realization.isoClass_hasRegularHighestWeight_iff

/-- A cuspidal class with regular highest weight has regular algebraic type. -/
theorem IsoClass.HasRegularHighestWeight.isRegularAlgebraic {c : IsoClass F r}
    (h : c.HasRegularHighestWeight) : c.IsRegularAlgebraic :=
  OperatorRealization.IsoClass.HasRegularHighestWeight.isRegularAlgebraic h

end CuspidalOperatorRealization

end Langlands.Automorphic
