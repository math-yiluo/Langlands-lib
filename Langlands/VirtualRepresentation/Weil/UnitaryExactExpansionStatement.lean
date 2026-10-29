import Langlands.VirtualRepresentation.Weil.ExactRealization

/-!
# Effective unitary exact expansion: statements

Every actual continuous unitarizable finite-dimensional complex representation
is asserted to have its whole exact class expanded by a nonnegative integral
combination of genuine unitary irreducible classes. These are proposition
definitions; only their definitional local specialization is proved here.
-/

noncomputable section

universe uG uV

namespace Langlands.VirtualRepresentation.Weil

variable (G : Type uG) [Group G] [TopologicalSpace G]

/-- Every actual continuous representation with an invariant positive Hermitian
form, of any rank and not assumed irreducible or semisimple, has its entire
exact class expanded by a coefficientwise nonnegative combination of genuine
continuous irreducible unitary classes. No uniqueness, chosen expansion or
decomposition is part of the statement. -/
def EffectiveUnitaryExactExpansionStatement : Prop :=
  ∀ (A : FiniteRepresentation.{0, uG, uV} ℂ G) (hc : A.IsContinuous), A.IsUnitary →
    ∃ x : UnitaryLattice.{uG, uV} G, x ∈ VirtualRepresentation.effective ∧
      ExactExpansion G (ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩)
        (includeUnitary G x)

end Langlands.VirtualRepresentation.Weil

namespace Langlands.VirtualRepresentation.LocalWeil

universe uF uW

open Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The same assertion for every actual continuous unitarizable representation
of the published local Weil group, using the existing local unitary lattice,
inclusion, exact quotient and expansion relation. -/
def EffectiveUnitaryExactExpansionStatement : Prop :=
  ∀ (A : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)) (hc : A.IsContinuous),
    A.IsUnitary →
    ∃ x : UnitaryLattice.{uF, uW} F, x ∈ VirtualRepresentation.effective ∧
      ExactExpansion F (ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩)
        (includeUnitary F x)

/-- The actual-local proposition is definitionally the generic one at the
published local Weil group. Neither side is asserted. -/
theorem effectiveUnitaryExactExpansion_iff :
    EffectiveUnitaryExactExpansionStatement.{uF, uW} F ↔
      Weil.EffectiveUnitaryExactExpansionStatement.{uF, uW} (localWeilGroup F) :=
  Iff.rfl

end Langlands.VirtualRepresentation.LocalWeil
