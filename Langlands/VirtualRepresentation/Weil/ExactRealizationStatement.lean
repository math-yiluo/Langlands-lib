import Langlands.VirtualRepresentation.Weil.ExactRealization

/-!
# Exact K0 realization and unique irreducible expansion: statements

The substantive bijectivity assertion is a proposition definition. Only its
logical equivalence with unique expansion is proved here.
-/

noncomputable section

universe uG uV

namespace Langlands.VirtualRepresentation.Weil

variable (G : Type uG) [Group G] [TopologicalSpace G]

/-- The canonical integral realization into the continuity-only exact quotient
is bijective. This is a statement, not a proof or a choice of inverse. -/
def ExactRealizationBijectiveStatement : Prop :=
  Function.Bijective (realizeExact.{uG, uV} G)

/-- Every exact virtual class has one and only one finite integral expansion in
genuine continuous irreducible classes. Coefficients need not be nonnegative. -/
def ExactExpansionUniqueStatement : Prop :=
  ∀ x : ContinuousExactGroup.{uG, uV} G,
    ∃! v : IrreducibleLattice.{uG, uV} G, ExactExpansion G x v

/-- The two formulations are logically equivalent; neither is asserted here. -/
theorem exactRealizationBijective_iff_uniqueExpansion :
    ExactRealizationBijectiveStatement.{uG, uV} G ↔
      ExactExpansionUniqueStatement.{uG, uV} G := by
  change Function.Bijective (realizeExact.{uG, uV} G) ↔
    ∀ x : ContinuousExactGroup.{uG, uV} G,
      ∃! v : IrreducibleLattice.{uG, uV} G, realizeExact G v = x
  constructor
  · intro h x
    obtain ⟨v, hv⟩ := h.2 x
    exact ⟨v, hv, fun w hw => h.1 (hw.trans hv.symm)⟩
  · intro h
    constructor
    · intro v w hvw
      obtain ⟨a, _, ha⟩ := h (realizeExact G v)
      exact (ha v rfl).trans (ha w hvw.symm).symm
    · intro x
      obtain ⟨v, hv, _⟩ := h x
      exact ⟨v, hv⟩

end Langlands.VirtualRepresentation.Weil

namespace Langlands.VirtualRepresentation.LocalWeil

universe uF uW

open Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Bijectivity for the already constructed local Weil group and exact quotient,
with the representation-carrier universe independent of the field universe. -/
def ExactRealizationBijectiveStatement : Prop :=
  Function.Bijective (realizeExact.{uF, uW} F)

/-- Unique exact expansion in the existing actual local irreducible lattice. -/
def ExactExpansionUniqueStatement : Prop :=
  ∀ x : ContinuousExactGroup.{uF, uW} F,
    ∃! v : Lattice.{uF, uW} F, ExactExpansion F x v

/-- The actual-local formulations inherit the generic logical equivalence. -/
theorem exactRealizationBijective_iff_uniqueExpansion :
    ExactRealizationBijectiveStatement.{uF, uW} F ↔
      ExactExpansionUniqueStatement.{uF, uW} F :=
  Weil.exactRealizationBijective_iff_uniqueExpansion (localWeilGroup F)

end Langlands.VirtualRepresentation.LocalWeil
