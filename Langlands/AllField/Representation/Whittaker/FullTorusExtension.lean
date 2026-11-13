import Langlands.Representation.Whittaker.FullTorusExtension
import Langlands.AllField.Representation.Whittaker.LastEntryOneAssembly
/-!
# Extending the Whittaker expansion to the full diagonal torus

Normalize the last entry, then use the common central character of all
Whittaker coefficient images. Finite-function closure and finite-fiber
regrouping preserve the uniform finite family and Schwartz–Bruhat coefficients.
-/

noncomputable section

namespace Langlands.AllField.WhittakerLastEntryOne
open Langlands.WhittakerLastEntryOne hiding assemble pullback_injective rootHom_rootLift rootLift_last rootLift_rootHom
open Langlands.AllField.WhittakerLastEntryOne

open scoped BigOperators

universe uA uB uK uV

end Langlands.AllField.WhittakerLastEntryOne

namespace Langlands.AllField.WhittakerFullTorus
open Langlands.WhittakerFullTorus hiding of_lastEntryOne
open Langlands.AllField.WhittakerFullTorus

open scoped BigOperators
open Langlands.WhittakerLastEntryOne (IsFiniteFunction torus roots)

universe uA uB uK uV

section Torus

variable {K : Type uK} [Field K] {n : ℕ}

variable [TopologicalSpace K]

variable [IsTopologicalRing K]

end Torus

/-- The exact last-entry-one target implies the unchanged full-torus target. -/
theorem of_lastEntryOne
    (hred : WhittakerLastEntryOneAsymptoticStatement.{uK, uV}) :
    WhittakerTypeAsymptoticStatement.{uK, uV} := by
  intro F _ T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro n V _ _ ρ ψ hcont hne hu hadm hfin
  dsimp only
  intro hspan
  let eligible : Module.Dual ℂ V → Prop := fun ℓ =>
    ∀ g : GeneralLinear (n + 1) F,
      ((∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1) →
      ∀ v, ℓ (ρ g v) = (∏ i : Fin n, ψ (g.val i.castSucc i.succ)) * ℓ v
  have hmem (ℓ : Module.Dual ℂ V) :
      ℓ ∈ Whittaker.functionals (GeneralLinear.upperUnipotent (n + 1) F)
        (Whittaker.entrywiseCharacter ψ (n + 1)) ρ ↔ eligible ℓ := by
    simpa only [eligible, Whittaker.EntrywiseEquivariant, and_imp] using
      Whittaker.mem_functionals_entrywiseCharacter_iff_entrywise ψ n ρ ℓ
  have hspan' : ∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧
      ℓ ∈ Whittaker.functionals (GeneralLinear.upperUnipotent (n + 1) F)
        (Whittaker.entrywiseCharacter ψ (n + 1)) ρ ∧
      ∀ ℓ' : Module.Dual ℂ V,
        ℓ' ∈ Whittaker.functionals (GeneralLinear.upperUnipotent (n + 1) F)
          (Whittaker.entrywiseCharacter ψ (n + 1)) ρ →
        ∃ c : ℂ, ℓ' = c • ℓ := by
    obtain ⟨ℓ, hne, heq, hspan⟩ := hspan
    exact ⟨ℓ, hne, (hmem ℓ).mpr heq,
      fun ℓ' hℓ' => hspan ℓ' ((hmem ℓ').mp hℓ')⟩
  obtain ⟨η, hη, hcentral⟩ := scalarCharacter_of_spanning_functional
    (Whittaker.coefficientCentralCharacter (GeneralLinear (n + 1) F))
    ρ (GeneralLinear.upperUnipotent (n + 1) F)
    (Whittaker.entrywiseCharacter ψ (n + 1)) hadm.1 hspan'
  obtain ⟨X, hX, hredX⟩ := hred F T n V ρ ψ hcont hne hu hadm hfin hspan
  exact extend_of_coefficient_character ρ eligible X hX hredX η hη
    (fun ℓ hℓ => hcentral ℓ ((hmem ℓ).mpr hℓ))

end Langlands.AllField.WhittakerFullTorus
