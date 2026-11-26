import Langlands.BushnellKutzko.CharacterIntertwining
import Langlands.BushnellKutzko.UnitFiltration

/-! # Determinant factorization of intertwined unit characters -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- The abstract-character extension of BK93 (2.4.11). A homomorphism on a
positive unit filtration subgroup intertwined by every ambient unit factors
through the determinant image. -/
def IntertwinedUnitCharacterStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (L : LatticeChain 𝒪[F] F V) (k : ℕ), 1 ≤ k →
    ∀ χ : L.unitFiltration k →* ℂˣ, (∀ g, g ∈ characterSelfIntertwining χ) →
      let det := (Units.map (LinearMap.det : Module.End F V →* F)).comp
        (L.unitFiltration k).subtype
      ∃ η : det.range →* ℂˣ, ∀ g, χ g = η (det.rangeRestrict g)

end Langlands.BushnellKutzko
