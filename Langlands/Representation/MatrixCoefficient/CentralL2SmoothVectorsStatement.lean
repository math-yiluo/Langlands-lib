import Langlands.Representation.MatrixCoefficient.CentralL2
import Langlands.Representation.Unitary.Completion
import Langlands.Representation.Smooth.SmoothPart.Definitions

/-! # `L²(G, χ, dg*)₀` is the space of smooth vectors of its Hilbert completion

Renard 2026, IV.3.1, Remark (printed p.99 / PDF p.105): the space `L²(G, χ, dg*)₀` of smooth
`χ`-covariant functions that are square integrable modulo the centre is the space of smooth
vectors in its Hilbert completion `L²(G, χ, dg*)`.
-/

noncomputable section

universe uG

open MeasureTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.3.1, Remark: let `G` be a t.d. group, `χ` a unitary character of `Z(G)` and `μ` a
Haar measure on `G / Z(G)`, also right invariant. For the published invariant positive form
`b = centralL2Form χ hχ μ` on `L²(G, χ, dg*)₀` (the integral over `G / Z(G)` of `f₁ f₂`-bar),
a vector of the Hilbert completion of `(L²(G, χ, dg*)₀, b)` has an open stabilizer under the
completed right-translation action exactly when it is the image of an element of
`L²(G, χ, dg*)₀`. -/
def CentralL2SmoothVectorsStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (χ : Subgroup.center G →* ℂˣ) (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1)
    [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    let b := Induction.centralL2Form χ hχ μ
    ∀ w : b.HilbertCompletion,
      w ∈ smoothVectors b.completedRepresentation ↔
        ∃ f : Induction.CentralL2 χ hχ μ, b.toHilbert f = w

end Langlands.Renard.CompactRepresentation
