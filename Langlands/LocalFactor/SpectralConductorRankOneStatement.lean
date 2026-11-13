import Langlands.LocalFactor.CommonClosureRankOneSpectral
import Langlands.ClassFieldTheory.Local.FiniteConductorStatement
import Langlands.LocalFactor.Ramification.InertiaPresentation

/-!
# Rank-one conductors at intermediate fields of the common closure

Statement only. For an intermediate field `L` of the common closure of `F`, a
finite Galois subfield `M ⊇ L`, a continuous character `χ` of `W_L` and a
character `ρ` of the inertia group of `M/L` that agrees with `χ` on inertia,
the inertia Artin sum of `ρ` (lower numbering of `M/L`, integer ring of `M`)
is the multiplicative conductor of the field character attached to `χ` by the
supplied normalized reciprocity component at `L`. This is local class field
theory in upper numbering (Serre, *Local Fields*, XV §2) with Hasse–Arf.
-/

noncomputable section

namespace Langlands.LocalFactor.SpectralConductor

open Ramification.Padic CommonClosure CommonClosureSpectralAnalytic Weil.Local

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Rank-one conductor transport at every intermediate field of the closure. -/
def CommonClosureRankOneConductorStatement : Prop :=
  ∀ (e : ReciprocityFamily F), NormalizedReciprocity F e →
  ∀ (L : Extension F)
    (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (hLM : L.field ≤ M.toIntermediateField) (χ : weilSubgroup F L →ₜ* ℂˣ),
    letI : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
    letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
      (IntermediateField.inclusion hLM).toAlgebra
    letI : IsScalarTower (Padic p) L.field (absoluteFiniteExtension F M).Carrier :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∀ ρ : inertia (absoluteFiniteExtension F M).canonicalTopologicalData L.field →* ℂˣ,
      (∀ (w : weilSubgroup F L), (w : localWeilGroup F) ∈ localInertia F →
        ∀ σ : inertia (absoluteFiniteExtension F M).canonicalTopologicalData L.field,
          (∀ y : (absoluteFiniteExtension F M).Carrier,
            ((σ : (absoluteFiniteExtension F M).Carrier ≃ₐ[L.field]
              (absoluteFiniteExtension F M).Carrier) y : AlgebraicClosure F.Carrier) =
              AlgEquiv.toAlgHom (localProjection F (w : localWeilGroup F))
                (y : AlgebraicClosure F.Carrier)) →
          ρ σ = χ w) →
      (inertiaArtinConductor (absoluteFiniteExtension F M).canonicalTopologicalData L.field
          (LocalClassField.rankOneCharacterRepresentation ρ) : ℚ) =
        ((fieldData F L).multiplicativeConductor (fieldCharacterEquiv F e L χ) : ℚ)

end Langlands.LocalFactor.SpectralConductor
