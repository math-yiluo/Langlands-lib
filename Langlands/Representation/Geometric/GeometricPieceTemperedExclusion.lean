import Langlands.Representation.Geometric.GeometricPieceUntwistedProjection
import Langlands.Representation.Exponents.RefinedUpperTemperedConeProof
import Langlands.Representation.Exponents.ReversedCoarseProjectionWeylRigidityProof

/-! Leading real-character exclusion on an actual raw reversed geometric piece. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear Exponents MeasureTheory
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

set_option maxHeartbeats 1600000 in
/-- A leading real character in an actual reversed upper-geometric piece of a
real-twisted tempered source can occur only for the inverse block reversal.
The divided fine real coordinates satisfy the blockwise tempered cone;
raw coarse-projection rigidity then identifies the representative. -/
theorem geometricPiece_tempered_leading_implies_reverse :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ [MeasurableSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
      [BorelSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
      (μ : Measure (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)))
      [μ.IsHaarMeasure] (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    IsTemperedModCenter A.representation μ →
    ∀ (t : Fin B.length → ℝ), StrictAnti t →
    ∀ (v : Equiv.Perm (Fin n)), IsMinimalRepresentative B B.reverse v →
    ∀ (S : BlockRefinement B) (R : BlockRefinement B.reverse)
      (hS : sourceLevi F.Carrier B B.reverse v = refinedLevi F.Carrier B S)
      (hR : sourceLevi F.Carrier B.reverse B v⁻¹ = refinedLevi F.Carrier B.reverse R),
    let At := SmoothRep.of (T.leviRealPowerTwist B t A.representation)
      ((T.isSmooth_leviRealPowerTwist_iff B t A.representation).mpr A.isSmooth)
    ∀ (χ : (Fin B.reverse.length → F.Carrierˣ) →* ℂˣ),
    IsGeneralizedEigencharacter
      ((((geometricPieceFunctor T B B.reverse v S R hS hR).obj At).ρ).comp
        (B.reverse.blockScalarLevi F.Carrier)) χ →
    T.IsRealPartOf χ (fun j => (B.reverse.size j : ℝ) * t j.rev) →
    v = B.reversePermutation.symm := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro _ _ μ _ A htemp t ht v hv S R hS hR
  dsimp only
  intro χ hχ hy
  obtain ⟨ψ, x, _hopen, hgen, hx, hproj⟩ :=
    geometricPiece_untwisted_real_projection T B B.reverse v S R hS hR
      A htemp.1 t χ _ hχ hy
  let xd : Fin n → ℝ := fun a =>
    x (blockIndex (B.flatten S) a) /
      ((B.flatten S).size (blockIndex (B.flatten S) a) : ℝ)
  have hcone : ∀ i : Fin B.length,
      IsClosedPositiveRootCone (fun a : Fin (B.size i) => xd (B.index i a)) := by
    intro i
    have hc := RefinedUpperTemperedCone.diagonalized_isClosedPositiveRootCone
      T B μ A.representation htemp S ψ hgen x hx i
    simpa only [xd, ProductLeviMinimalIndex.blockIndex_flatten_index,
      BlockShape.flatten_size_flattenBlockEquiv] using hc
  apply reversedCoarseProjectionWeylRigidity n B t v xd ht hv hcone
  intro i
  obtain ⟨j, rfl⟩ := Fin.rev_surjective i
  change (∑ a : Fin (B.size j.rev),
      (xd (v.symm (B.reversePermutation.symm (B.index j.rev a))) +
        t (blockIndex B (v.symm (B.reversePermutation.symm (B.index j.rev a)))))) =
      (B.size j.rev : ℝ) * t j.rev
  have hp := hproj j
  change (∑ a : Fin (B.size j.rev),
      (xd (v.symm (B.reverse.index j a)) +
        t (blockIndex B (v.symm (B.reverse.index j a))))) =
      (B.size j.rev : ℝ) * t j.rev at hp
  simpa only [B.reversePermutation_symm_index] using hp

end Langlands.Geometric
