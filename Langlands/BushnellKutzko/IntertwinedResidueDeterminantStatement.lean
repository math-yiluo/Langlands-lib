import Langlands.BushnellKutzko.CharacterIntertwining
import Langlands.BushnellKutzko.UnitFiltration

/-! # The residue determinant of an intertwined character -/

open ValuativeRel IsLocalRing

namespace Langlands.BushnellKutzko

universe uF uV

/-- A character of the units of a lattice-chain order that is trivial at depth one and intertwined
by every ambient automorphism factors through the residue of the determinant. -/
def IntertwinedResidueDeterminantStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (L : LatticeChain 𝒪[F] F V) (ξ : L.unitFiltration 0 →* ℂˣ),
    (∀ x : L.unitFiltration 0, x.val ∈ L.unitFiltration 1 → ξ x = 1) →
    (∀ y, y ∈ characterSelfIntertwining ξ) →
    ∃ χ : (ResidueField 𝒪[F])ˣ →* ℂˣ,
      ∀ (x : L.unitFiltration 0) (a : 𝒪[F]ˣ),
        ((a : 𝒪[F]) : F) = LinearMap.det (x.val : Module.End F V) →
        ξ x = χ (Units.map (residue 𝒪[F]) a)

end Langlands.BushnellKutzko
