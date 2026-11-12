import Langlands.Representation.CompactCoefficient.CompactFormalDegreeStatements

/-! # Dependence of the formal degree on the Haar measure (Renard IV.1.4, Remark 1)

The formal degree `d(τ) = κ(τ)⁻¹` of IV.1.4 is defined by the identity
`τ(ˇφ_{w,λ}) x = κ(τ) λ(x) w`, in which the Hecke action integrates against a Haar measure
`μ`. Replacing `μ` by `c μ` (`c > 0`) multiplies `κ(τ)` by `c`, so `d(τ)` becomes `d(τ)/c`.
-/

noncomputable section

universe u v

open CategoryTheory MeasureTheory
open scoped NNReal

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.1.4, Remark 1: the formal degree depends on the Haar measure. For a Hausdorff,
locally compact, totally disconnected group `G` with a Haar measure `μ`, a smooth
representation `τ`, a positive real `c` and a complex `κ`, the formal-degree identity
`τ(ˇφ_{w,λ}) x = κ λ(x) w` of IV.1.4 (ii) holds for `μ` exactly when the identity with `c κ`
holds for `c μ`. Hence `κ_{cμ}(τ) = c κ_μ(τ)` and `d_{cμ}(τ) = d_μ(τ)/c`. -/
def CompactFormalDegreeHaarScalingStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (τ : SmoothRep.{0, u, v} ℂ G) (c : ℝ≥0) [NeZero c] (κ : ℂ),
    haveI : (c • μ).IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul μ (NeZero.ne c)
    ((∀ (w : τ) (ℓ : SmoothDual τ.representation) (f : Hecke.HeckeAlgebra μ),
        (∀ g : G, f g = (ℓ : Module.Dual ℂ τ) (τ.representation g⁻¹ w)) → ∀ x : τ,
          Hecke.heckeAction μ τ.representation τ.isSmooth f x =
            (κ * (ℓ : Module.Dual ℂ τ) x) • w) ↔
      ∀ (w : τ) (ℓ : SmoothDual τ.representation) (f : Hecke.HeckeAlgebra (c • μ)),
        (∀ g : G, f g = (ℓ : Module.Dual ℂ τ) (τ.representation g⁻¹ w)) → ∀ x : τ,
          Hecke.heckeAction (c • μ) τ.representation τ.isSmooth f x =
            (((c : ℝ) : ℂ) * κ * (ℓ : Module.Dual ℂ τ) x) • w)

end Langlands.Renard.CompactRepresentation
