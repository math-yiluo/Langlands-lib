import Langlands.Group.HaarModulus
import Langlands.Group.GL.PadicBlocks
import Langlands.Representation.Parabolic.UnipotentFiniteContainment

/-! The actual Haar modulus of a product-Levi refinement radical. -/

open scoped NNReal
open MeasureTheory

namespace Langlands.PadicField.TopologicalData

universe uF
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The actual refinement radical is locally compact for the supplied topology,
through the published continuous equivalence with the finite product of block radicals. -/
theorem refinedUnipotentLocallyCompactSpace (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    LocallyCompactSpace (Geometric.refinedUnipotent F.Carrier B S) := by
  let := T.topology
  have : ∀ i, LocallyCompactSpace ((S i).unipotentRadical F.Carrier) :=
    fun i => T.unipotentRadicalLocallyCompactSpace (S i)
  exact (Geometric.refinedUnipotentRadicalEquiv B S F.Carrier).toHomeomorph.isOpenEmbedding.locallyCompactSpace

end Langlands.PadicField.TopologicalData

namespace Langlands.Geometric

universe uF

/-- For every refinement `S` of a block shape `B`, conjugation by an actual refined
Levi element `m` pushes every Borel Haar measure on the actual refinement radical
forward to `(T.refinedLeviModulus B S m)⁻¹` times itself, and the actual normalizer
Haar character restricted to the refined Levi is `T.refinedLeviModulus B S`.
This internal, derived proposition is a statement, not a proof. -/
def PadicRefinedUnipotentHaarModulus : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (B : GeneralLinear.BlockShape n) (S : BlockRefinement B),
    letI := T.topology
    letI := T.leviTopologicalGroup B
    letI := T.refinedUnipotentLocallyCompactSpace B S
    (∀ (m : refinedLevi F.Carrier B S)
      [MeasurableSpace (refinedUnipotent F.Carrier B S)]
      [BorelSpace (refinedUnipotent F.Carrier B S)]
      (μ : Measure (refinedUnipotent F.Carrier B S)) [μ.IsHaarMeasure],
      μ.map (HaarModulus.normalizerConj (refinedUnipotent F.Carrier B S)
          (refinedLeviNormalizer F.Carrier B S m)) =
        ((T.refinedLeviModulus B S m : ℝ≥0)⁻¹) • μ) ∧
    (HaarModulus.normalizerCharacter (refinedUnipotent F.Carrier B S)).comp
        (refinedLeviNormalizer F.Carrier B S) =
      T.refinedLeviModulus B S

end Langlands.Geometric
