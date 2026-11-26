import Langlands.BushnellKutzko.SimpleStratumGroups

/-! # Relative unit double cosets (BK93 (1.6.1)) -/

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uV

/-- For the centralizer of an element that generates a normalizing subfield,
intersecting a positive-depth unit double coset with the centralizer units
recovers the relative unit double coset. -/
def RelativeUnitDoubleCosetStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (L : LatticeChain 𝒪[F] F V) (β : Module.End F V) (hE : IsField (elementAlgebra β)),
    letI := hE.toField
    (∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ L.stabilizer) →
    ∀ m : ℕ, 1 ≤ m → ∀ y ∈ centralizerUnitGroup β,
      let G := (Module.End F V)ˣ
      let U : Set G := L.unitFiltration m
      let Urel : Set G := relativeUnitFiltration L β m
      (U * {y} * U) ∩ (centralizerUnitGroup β : Set G) = Urel * {y} * Urel

end Langlands.BushnellKutzko
