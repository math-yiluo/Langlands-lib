import Langlands.Global.LeftCosetProduct
import Langlands.Global.LeftCosetFundamentalDomain
import Mathlib.MeasureTheory.Measure.Prod

/-! # Product measure on a discrete left quotient with an unquotiented factor -/

noncomputable section

set_option autoImplicit false

open MeasureTheory Topology

namespace Langlands.Global.LeftCosetSpace

universe u v w

/-- Transport the ambient product through `E` and quotient by `{1} × H` with counting
normalization. The resulting measure corresponds exactly to the product of the `A` measure
and the discrete left quotient measure of `N`, without a scalar. -/
def ProductQuotientMeasureStatement : Prop :=
  ∀ {A : Type u} {N : Type v} {G : Type w} [Group A] [Group N] [Group G]
    [TopologicalSpace A] [TopologicalSpace N] [TopologicalSpace G]
    [IsTopologicalGroup N] [IsTopologicalGroup G]
    [MeasurableSpace A] [MeasurableSpace N] [MeasurableSpace G]
    [BorelSpace A] [BorelSpace N] [BorelSpace G]
    [SecondCountableTopology N] [SecondCountableTopology G]
    (E : A × N ≃ₜ* G) (H : Subgroup N) (Γ : Subgroup G)
    (hΓ : ∀ p, E p ∈ Γ ↔ p.1 = 1 ∧ p.2 ∈ H)
    (hHdisc : IsDiscrete (H : Set N)) (hΓdisc : IsDiscrete (Γ : Set G))
    (μA : Measure A) (μN : Measure N) [SFinite μA] [SFinite μN]
    (μG : Measure G) [SMulInvariantMeasure Γ G μG],
    MeasurePreserving E (μA.prod μN) μG →
    MeasurePreserving (productHomeomorph E H Γ hΓ)
      (discreteQuotientMeasure Γ hΓdisc μG) (μA.prod (discreteQuotientMeasure H hHdisc μN))

end Langlands.Global.LeftCosetSpace
