import Langlands.Representation.Classification.TadicUnitaryStatement
import Langlands.Representation.Whittaker.FiniteProductCriterion
import Langlands.Representation.Whittaker.AlgebraicTwist
import Langlands.Representation.Derivative.TopLocalizationData

/-! # Whittaker nondegeneracy of actual twisted and complementary products -/

noncomputable section

namespace Langlands

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

namespace Whittaker

/-- A determinant real-power twist retains the entire all-rank upper-character
functional space by keeping each underlying linear functional. -/
def segmentFactorFunctionalsEquiv {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)) (s : ℝ) :
    letI := T.topology
    functionals (upperUnipotent n F.Carrier) (entrywiseCharacter ψ.complex n)
      π.representation ≃ₗ[ℂ]
        functionals (upperUnipotent n F.Carrier) (entrywiseCharacter ψ.complex n)
          (T.segmentFactor π s).representation := by
  let := T.topology
  exact twistFunctionalEquiv (upperUnipotent n F.Carrier)
    (entrywiseCharacter ψ.complex n) (T.determinantPowerCharacter n s)
      (Derivative.TopLocalization.realPowerCharacter_upper T s) π.representation

/-- A real determinant twist preserves existence of an all-rank
upper-character functional on the original representation. -/
theorem hasFunctional_segmentFactor_iff {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)) (s : ℝ) :
    letI := T.topology
    HasFunctional (N := upperUnipotent n F.Carrier)
      (θ := entrywiseCharacter ψ.complex n) (T.segmentFactor π s).representation ↔
        HasFunctional (N := upperUnipotent n F.Carrier)
          (θ := entrywiseCharacter ψ.complex n) π.representation := by
  let := T.topology
  rw [hasFunctional_iff_nontrivial, hasFunctional_iff_nontrivial]
  exact Equiv.nontrivial_congr (segmentFactorFunctionalsEquiv T ψ π s).symm.toEquiv

/-- Nondegeneracy of a finite normalized product of real twists is equivalent
to nondegeneracy of every original untwisted factor, in every ambient rank. -/
theorem hasFunctional_twistedProduct_iff {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (s : Fin B.length → ℝ) :
    letI := T.topology
    HasFunctional (N := upperUnipotent n F.Carrier)
      (θ := entrywiseCharacter ψ.complex n)
      (T.twistedProductInduced B σ s).representation ↔
        ∀ i, HasFunctional (N := upperUnipotent (B.size i) F.Carrier)
          (θ := entrywiseCharacter ψ.complex (B.size i)) (σ i).representation := by
  let := T.topology
  exact (hasFunctional_finiteProduct_iff.{uF,uV} T ψ B
    (T.twistedBlocks B σ s)).trans
      (forall_congr' fun i => hasFunctional_segmentFactor_iff T ψ (σ i) (s i))

end Whittaker

namespace Classification.SpehDatum

/-- The entire complementary induction of a supplied representation has a
nonzero Whittaker functional exactly when that representation does. -/
theorem hasFunctional_complementaryInduced_iff (d : SpehDatum.{uF,uV} F T)
    (S : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear d.degree F.Carrier))
    (α : ℝ) :
    letI := T.topology
    Whittaker.HasFunctional (N := upperUnipotent (2 * d.degree) F.Carrier)
      (θ := Whittaker.entrywiseCharacter ψ.complex (2 * d.degree))
      (d.complementaryInduced S α).representation ↔
        Whittaker.HasFunctional (N := upperUnipotent d.degree F.Carrier)
          (θ := Whittaker.entrywiseCharacter ψ.complex d.degree) S.representation := by
  let := T.topology
  exact (Whittaker.hasFunctional_twistedProduct_iff.{uF,uV} T ψ
    (BlockShape.uniform 2 d.degree (Nat.mul_pos d.length_pos d.rank_pos))
    (fun _ => S) (fun i => if (i : ℕ) = 0 then α else -α)).trans
      ⟨fun h => h (0 : Fin 2), fun h _ => h⟩

end Classification.SpehDatum

end Langlands
