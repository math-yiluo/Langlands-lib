import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Jacquet.LocalizationExactnessStatement

namespace Langlands.Jacquet.Localization

universe uG uV

/-- A finite smooth representation filtration collapses after character
localization when all actual graded quotients except a chosen one vanish. -/
def FiltrationCollapseStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    IsLimitOfCompactSubgroups (⊤ : Subgroup G) →
    ∀ (θ : G →* ℂˣ), IsLocallyConstant (fun g => (θ g : ℂ)) →
    ∀ (A : Rep.{uV} ℂ G), IsSmooth A.ρ →
    ∀ (m : ℕ) (s : ObjectRepFiltration A m) (j : Fin m),
      (∀ i : Fin m, i ≠ j →
        Subsingleton (Coinvariants (s.gradedRepresentation i).ρ
          (⊤ : Subgroup G) (θ.comp (⊤ : Subgroup G).subtype))) →
      Nonempty
        (Coinvariants A.ρ (⊤ : Subgroup G) (θ.comp (⊤ : Subgroup G).subtype) ≃ₗ[ℂ]
          Coinvariants (s.gradedRepresentation j).ρ
            (⊤ : Subgroup G) (θ.comp (⊤ : Subgroup G).subtype))

end Langlands.Jacquet.Localization
