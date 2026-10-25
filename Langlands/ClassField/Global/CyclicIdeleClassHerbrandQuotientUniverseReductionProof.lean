import Langlands.ClassField.Global.CyclicIdeleClassHerbrandQuotientUniverseReductionStatement
import Langlands.ClassField.Global.IdeleClassBaseImage

/-! # Proof of the idele-class Herbrand universe reduction -/

noncomputable section

namespace Langlands.ClassField.Global

/-- Transfer the common-universe assertion through the image of the base field. -/
theorem cyclicIdeleClassHerbrandQuotientUniverseReduction.{u, v} :
    CyclicIdeleClassHerbrandQuotientUniverseReduction.{u, v} := by
  intro h F _ _ E _ _ _ _ _
  let F₀ := (⊥ : IntermediateField F E)
  let : IsCyclic (E ≃ₐ[F₀] E) :=
    (baseImageAutEquiv F E).isCyclic.mp inferInstance
  obtain ⟨h₁, h₂, hcard⟩ := h F₀ E
  let e₁ := (relativeIdeleClassCohomologyBaseImageIso F E 1).toLinearEquiv.toEquiv
  let e₂ := (relativeIdeleClassCohomologyBaseImageIso F E 2).toLinearEquiv.toEquiv
  have := h₁
  have := h₂
  refine ⟨Finite.of_equiv _ e₁.symm, Finite.of_equiv _ e₂.symm, ?_⟩
  calc
    Nat.card (relativeIdeleClassCohomology F E 2 : Type v) =
        Nat.card (relativeIdeleClassCohomology F₀ E 2 : Type v) := Nat.card_congr e₂
    _ = Module.finrank F₀ E *
        Nat.card (relativeIdeleClassCohomology F₀ E 1 : Type v) := hcard
    _ = Module.finrank F E *
        Nat.card (relativeIdeleClassCohomology F E 1 : Type v) := by
      rw [IntermediateField.finrank_bot', ← Nat.card_congr e₁]

end Langlands.ClassField.Global
