import Langlands.Representation.CyclicSpan
import Langlands.Representation.Smooth.Factorization.RestrictedProductExistenceStatement

/-! # Simultaneous cyclic local factors for a restricted-product representation -/

noncomputable section
open scoped Classical

namespace Langlands

open RestrictedTensor MeasureTheory

universe uI uG uV

/-- A common nonzero vector generates all the required irreducible admissible
local factors, and is fixed by a full reference tail. -/
def FlathCyclicVectorSelectionStatement : Prop :=
  ∀ (ι : Type uI) (G : ι → Type uG) [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)]
    [∀ i, TotallyDisconnectedSpace (G i)]
    [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    (μ : ∀ i, Measure (G i)) [∀ i, Measure.IsHaarMeasure (μ i)]
    [∀ i, Measure.Regular (μ i)]
    (H : ∀ i, Subgroup (G i))
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (RestrictedGroup G H) V),
    (∀ i, IsOpen (H i : Set (G i)) ∧ IsCompact (H i : Set (G i))) →
    (∀ᶠ i in Filter.cofinite, SphericalHeckeCommutative (μ i) (H i)) →
    IsAdmissible π → π.IsIrreducible →
    ∃ (E : Finset ι) (v : V), v ≠ 0 ∧
      (∀ g : RestrictedGroup G H,
        (∀ i ∈ E, g i = 1) → (∀ i ∉ E, g i ∈ H i) → π g v = v) ∧
      (∀ i,
        let σ := π.comp (RestrictedProduct.mulSingleMonoidHom H i)
        IsAdmissible (Cyclic.orbitSpan σ v).toRepresentation ∧
          (Cyclic.orbitSpan σ v).toRepresentation.IsIrreducible) ∧
      (∀ i ∉ E,
        let σ := π.comp (RestrictedProduct.mulSingleMonoidHom H i)
        v ∈ fixedVectors σ (H i) ∧
          Module.finrank ℂ
            (fixedVectors (Cyclic.orbitSpan σ v).toRepresentation (H i)) = 1)

end Langlands
