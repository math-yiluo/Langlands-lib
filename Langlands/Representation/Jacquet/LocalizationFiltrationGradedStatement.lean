import Langlands.Representation.Jacquet.LocalizationFiltration
import Langlands.Representation.Jacquet.LocalizationExactnessStatement
import Langlands.Representation.Filtration.ObjectDefinitions

/-! Actual image filtrations and character-localized graded quotients. -/

namespace Langlands.Jacquet.Localization

universe uG uV

/-- The actual image filtration of a smooth representation under character
localization has the localized original graded representations as its actual
successive quotients, with their normalizing-subgroup actions. -/
def ImageFiltrationGradedStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G), IsLimitOfCompactSubgroups U →
    ∀ (θ : U →* ℂˣ), IsLocallyConstant (fun u : U => (θ u : ℂ)) →
    ∀ (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)
      (hθ : IsInvariant U M hMU θ) (A : Rep.{uV} ℂ G),
      IsSmooth A.ρ →
      ∀ (n : ℕ) (s : ObjectRepFiltration A n),
        ∃ t : ObjectRepFiltration (Rep.of (action A.ρ U θ M hMU hθ)) n,
          (∀ k : Fin (n + 1),
            t.subrepresentation k =
              imageSubrepresentation U θ M hMU hθ A.ρ (s.subrepresentation k)) ∧
          ∀ i : Fin n,
            Nonempty ((t.gradedRepresentation i).ρ.Equiv
              (action (s.gradedRepresentation i).ρ U θ M hMU hθ))

end Langlands.Jacquet.Localization
