import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.Definitions
import Langlands.LocalField.Normalization.Definitions

/-! # Zero-depth ramification in terms of supplied local-field data -/

namespace Langlands.LocalClassField.NYLL

/-- For a finite Galois extension of universe-zero p-adic fields, the zeroth
upper ramification group, built from the supplied base realization, consists
exactly of the automorphisms fixing every integral residue class of an
arbitrary supplied extension realization. -/
def ZeroUpperRamificationHostStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F E : PadicField.{0} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier] [IsGalois F.Carrier E.Carrier]
    (TF : F.TopologicalData) (TE : E.TopologicalData) (σ : Gal(E.Carrier/F.Carrier)),
    letI := TF.topology
    letI := TF.valuativeRel
    letI := TF.localField
    σ ∈ Langlands.NYLL.RamificationTheory.LocalField.localUpperRamificationGroup
        F.Carrier E.Carrier 0 ↔
      ∀ x : E.Carrier, TE.discreteValuation x ≤ 1 →
        TE.discreteValuation (σ x - x) < 1

end Langlands.LocalClassField.NYLL
