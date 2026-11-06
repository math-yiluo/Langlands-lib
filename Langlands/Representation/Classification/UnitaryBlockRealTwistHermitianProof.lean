import Langlands.Representation.Classification.UnitaryAdmissibleHermitianProof
import Langlands.Representation.Classification.TwistedProductOrdinaryDualProof

/-!
# Hermitian duality of real twists of unitary blocks

The positive form on an admissible unitary block identifies its opposite real
norm twist with the smooth dual of its given norm twist, conjugate-linearly
and by the original evaluation pairing.
-/

noncomputable section

namespace Langlands.Classification

universe uF uV

/-- For an actual unitary square-integrable block, the original positive form
pairs the twists with opposite real exponents by Hermitian duality. -/
theorem unitaryBlockRealTwistHermitianClause {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    UnitaryBlockRealTwistHermitianClause.{uF, uV} F T := by
  intro n _
  let _ := T.topology
  let _ := T.generalLinearTopologicalGroup n
  intro δ _ hδ b s
  let H := b.smoothDualEquiv (GeneralLinear.compactOpen_cofinal F T n)
    hδ.isAdmissible
  let D := segmentFactorSmoothDualEquiv F T δ s
  let E : δ ≃ₗ⋆[ℂ] SmoothDual (T.segmentFactor δ s).representation :=
    H.trans D.symm.toLinearEquiv
  refine ⟨E, ?_, fun _ _ => rfl⟩
  intro g v
  have hH : H ((T.segmentFactor δ (-s)).representation g v) =
      twist (T.determinantPowerCharacter n (-s))
        (smoothContragredient δ.representation) g (H v) := by
    change H ((realPowerCharacter (T.determinantNorm n) (-s) g : ℂ) •
      δ.representation g v) =
        (realPowerCharacter (T.determinantNorm n) (-s) g : ℂ) •
          smoothContragredient δ.representation g (H v)
    rw [map_smulₛₗ]
    simp only [coe_realPowerCharacter, starRingEnd_apply]
    congr 1
    · exact Complex.conj_ofReal _
    · exact b.toSmoothDual_apply_action hδ.isAdmissible.1 g v
  change D.symm (H ((T.segmentFactor δ (-s)).representation g v)) =
    smoothContragredient (T.segmentFactor δ s).representation g (D.symm (H v))
  rw [hH]
  exact Representation.IntertwiningMap.isIntertwining _ _ D.symm.toIntertwiningMap g (H v)

end Langlands.Classification
