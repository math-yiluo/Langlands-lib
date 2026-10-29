import Langlands.Representation.Geometric.IntersectionCoordinateTopology
import Langlands.Representation.Geometric.RefinedUnipotentHaarStatement

/-! The Haar modulus on the actual unipotent intersection, in refined coordinates. -/

open scoped NNReal
open MeasureTheory

namespace Langlands.PadicField.TopologicalData

universe uF
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Local compactness of the actual ambient intersection, transported from the
published refined radical through its canonical continuous equivalence. -/
theorem intersectionUnipotentLocallyCompactSpace (T : F.TopologicalData) {n : ℕ}
    (B C : GeneralLinear.BlockShape n) (w : Equiv.Perm (Fin n))
    (S : Geometric.BlockRefinement B)
    (hS : Geometric.IsIntersectionRefinement (F := F.Carrier) B C w S) :
    letI := T.topology
    LocallyCompactSpace
      (Geometric.intersectionSource (B.leviSubgroup F.Carrier)
        (C.unipotentSubgroup F.Carrier) (GeneralLinear.permutation n F.Carrier w)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.refinedUnipotentLocallyCompactSpace B S
  let e := Geometric.refinedUnipotentIntersectionEquiv F.Carrier B C w S hS
  exact e.symm.toHomeomorph.isOpenEmbedding.locallyCompactSpace

end Langlands.PadicField.TopologicalData

namespace Langlands.Geometric

universe uF

/-- The actual intersection-Levi action scales every supplied Haar measure on
the actual unipotent intersection by the inverse explicit refined modulus.
Its positive normalizer character is the same explicit modulus after canonical
Levi transport. This proposition is an internal derived statement. -/
def PadicIntersectionUnipotentHaarModulus : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (B C : GeneralLinear.BlockShape n) (w : Equiv.Perm (Fin n))
    (S : BlockRefinement B)
    (hS : IsIntersectionRefinement (F := F.Carrier) B C w S),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.generalLinearTopologicalGroup n
    letI := T.intersectionUnipotentLocallyCompactSpace B C w S hS
    let M := B.leviSubgroup F.Carrier
    let N := C.leviSubgroup F.Carrier
    let V := C.unipotentSubgroup F.Carrier
    let g := GeneralLinear.permutation n F.Carrier w
    let U := intersectionSource M V g
    let ι := General.intersectionToCorrectionNormalizer M N M V g M.le_normalizer
      (C.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
    let eL := refinedLeviIntersectionEquiv F.Carrier B C w S hS
    (∀ (m : General.intersectionIn M N g)
      [MeasurableSpace U] [BorelSpace U] (μ : Measure U) [μ.IsHaarMeasure],
      μ.map (HaarModulus.normalizerConj U (ι m)) =
        ((T.refinedLeviModulus B S (eL.symm m) : ℝ≥0)⁻¹) • μ) ∧
    ((HaarModulus.normalizerCharacter U).comp ι).comp eL.toMulEquiv.toMonoidHom =
      T.refinedLeviModulus B S

end Langlands.Geometric
