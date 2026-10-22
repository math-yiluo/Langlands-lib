import Langlands.Representation.Jacquet.Localization
import Mathlib.Basic.Complex.Basic
import Mathlib.Topology.LocallyConstant.Basic

namespace Langlands.Jacquet.Localization

universe uG uV uW uX

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

/-- BZ77's literal condition that every compact subset lies in a compact subgroup. -/
def IsLimitOfCompactSubgroups (U : Subgroup G) : Prop :=
  ∀ C : Set U, IsCompact C →
    ∃ K : Subgroup U, IsCompact (K : Set U) ∧ C ⊆ (K : Set U)

/-- Every character relation is detected in one actual compact subgroup.
This finite-span prerequisite does not require smoothness or local constancy. -/
def CompactCharacterRelationDetectionClause : Prop :=
  ∀ (U : Subgroup G), IsLimitOfCompactSubgroups U →
    ∀ (θ : U →* ℂˣ) (ρ : Representation ℂ G V) (v : V),
      v ∈ relations ρ U θ ↔
        ∃ K : Subgroup U, IsCompact (K : Set U) ∧
          v ∈ relations (ρ.comp U.subtype) K (θ.comp K.subtype)

/-- Exactness of the actual character-localized quotient maps with their
unnormalized normalizing-subgroup actions, over complex coefficients. -/
def CharacterLocalizationExactnessClause : Prop :=
  ∀ [IsTopologicalGroup G],
    ∀ (U : Subgroup G), IsLimitOfCompactSubgroups U →
      ∀ (θ : U →* ℂˣ), IsLocallyConstant (fun u : U => (θ u : ℂ)) →
        ∀ (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)
          (hθ : IsInvariant U M hMU θ)
          (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
          (τ : Representation ℂ G X)
          (i : ρ.IntertwiningMap σ) (p : σ.IntertwiningMap τ),
          Function.Injective i → Function.Surjective p →
          LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap →
          IsSmooth σ →
          Function.Injective (map U θ M hMU hθ i) ∧
          LinearMap.range (map U θ M hMU hθ i).toLinearMap =
            LinearMap.ker (map U θ M hMU hθ p).toLinearMap ∧
          Function.Surjective (map U θ M hMU hθ p)

/-- Compact detection and exactness of character localization on actual quotients. -/
def CharacterLocalizationExactnessStatement : Prop :=
  CompactCharacterRelationDetectionClause (G := G) (V := V) ∧
    CharacterLocalizationExactnessClause (G := G) (V := V) (W := W) (X := X)

end Langlands.Jacquet.Localization
