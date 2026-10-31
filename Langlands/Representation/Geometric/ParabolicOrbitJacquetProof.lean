import Langlands.Representation.Geometric.ParabolicOrbitJacquetStatement
import Langlands.Representation.Geometric.ParabolicOrbitCompactComparison

/-! The natural normalized comparison for the actual parabolic orbit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.PadicField.TopologicalData

open CategoryTheory GeneralLinear Geometric Induction

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : MinimalRepresentatives B C) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : IsIntersectionRefinement (F := F.Carrier) B C w.val S)
  (hR : IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ R)

/-- The actual orbit integral, target normalization and refined induction form
one natural isomorphism on the full smooth source category. -/
theorem parabolicOrbitJacquetComparison :
    letI := T.topology
    Nonempty (parabolicOrbitJacquetFunctor.{uF, uV} T B C w.val ≅
      geometricPieceFunctor T B C w.val S R hS.2.1 hR.2.1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  have hE := T.parabolicOrbitCompactComparison_exists.{uF, uV} B C w.val
  obtain ⟨E, hE⟩ := hE
  rw [T.geometricPieceFunctor_eq_pullback B C w S R hS hR]
  refine ⟨NatIso.ofComponents (fun A => Rep.mkIso
    ((twistEquiv (Jacquet.inverseHalfCharacter (T.leviModulus C)) (E A)).trans
      (T.parabolicOrbitInductionTransportEquiv B C w S R hS hR A.representation))) ?_⟩
  intro A A' f
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  change T.parabolicOrbitInductionTransportEquiv B C w S R hS hR A'.representation
      (E A' (Parabolic.leviCoinvariantsMap C
        (compactInducedMap (parabolicOrbitStabilizer F.Carrier B C w.val)
          (parabolicOrbitCoefficientMap F.Carrier B C w.val (T.leviHalfModulus B)
            (SmoothRep.hom f))) z)) =
    T.normalizedRefinedInducedMap C R
      (refinedIntersectionTransportMap F.Carrier B C w.val S R hS.2.1 hR.2.1
        (T.normalizedRefinedJacquetMap B S (SmoothRep.hom f)))
      (T.parabolicOrbitInductionTransportEquiv B C w S R hS hR A.representation
        (E A z))
  have h₁ := hE A A' f z
  have h₂ := T.parabolicOrbitInductionTransportEquiv_natural B C w S R hS hR
    (SmoothRep.hom f) (E A z)
  exact (congrArg (fun q => T.parabolicOrbitInductionTransportEquiv B C w S R hS hR
    A'.representation q) h₁).trans h₂

end Langlands.PadicField.TopologicalData

namespace Langlands.Geometric

universe uF uV

/-- BZ77's local comparison, with all normalizing characters cancelled, for
all supplied actual p-adic data and all smooth complex source representations. -/
theorem padicParabolicOrbitJacquetComparison :
    PadicParabolicOrbitJacquetComparison.{uF, uV} := by
  intro p hp F T n hn B C
  let := T.topology
  intro w S R hS hR
  exact T.parabolicOrbitJacquetComparison B C w S R hS hR

end Langlands.Geometric
