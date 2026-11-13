import Langlands.Representation.Classification.LanglandsData

/-!
# Local isobaric sums for `GL_n` over a p-adic field

The isobaric sum `π_1 ⊞ ⋯ ⊞ π_k` of irreducible representations `π_i` of
`GL_(n_i)(F)` (Getz–Hahn 2024, §10.6, (10.33)) is the Langlands quotient attached
to the union of the Langlands data of the `π_i`. In Zelevinsky's segment form:
if `π_i` is the Langlands quotient `Q(a_i)` of the multisegment `a_i`, then
`π_1 ⊞ ⋯ ⊞ π_k` is `Q(a_1 + ⋯ + a_k)`. The isobaric sum is recorded only by a
relation: neither existence nor uniqueness is assumed.
-/

noncomputable section

namespace Langlands

universe uV uF

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- `τ` is an isobaric sum `π_1 ⊞ ⋯ ⊞ π_k`: there are multisegments `a_i` such
that each `π_i` is a Langlands quotient attached to `a_i` and `τ` is a Langlands
quotient attached to the multiset sum `a_1 + ⋯ + a_k`, all in the head form
`Multisegment.IsLanglandsHead`. -/
def IsIsobaricSum {k : ℕ} {n : Fin k → ℕ} {N : ℕ}
    (π : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n i) F.Carrier))
    (τ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)) : Prop :=
  ∃ a : Fin k → Multisegment.{uV, uF} T,
    (∀ i, (a i).IsLanglandsHead (π i)) ∧ (∑ i, a i).IsLanglandsHead τ

variable {T}

/-- An isobaric sum is irreducible. -/
theorem IsIsobaricSum.isIrreducible {k : ℕ} {n : Fin k → ℕ} {N : ℕ}
    {π : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n i) F.Carrier)}
    {τ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (h : T.IsIsobaricSum π τ) :
    letI := T.topology
    τ.representation.IsIrreducible := by
  obtain ⟨_, _, _, _, _, _, hτ⟩ := h
  exact hτ.1

end PadicField.TopologicalData

end Langlands
