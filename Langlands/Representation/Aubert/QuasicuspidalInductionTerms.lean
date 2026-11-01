import Langlands.Representation.Aubert.QuasicuspidalCutSupport

/-! Individual induction--Jacquet terms on a quasicuspidally induced class. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Langlands.Aubert

open GeneralLinear Geometric Parabolic SmoothRep CuspidalSupport
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- In positive rank each individual induction-after-Jacquet term sends a
quasicuspidally induced class to a nonnegative integral multiple of that class. -/
def QuasicuspidalInductionTermsStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n → ∀ (B C : BlockShape n)
    (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier))
    (hA : A.HasFiniteLength),
    IsLeviQuasicuspidal B A.representation →
    ∃ r : ℕ,
      normalizedInductionK0.{uF, uV} F T C
          (normalizedJacquetK0.{uF, uV} F T C
            (normalizedInductionK0.{uF, uV} F T B
              (B.finiteLengthClass F.Carrier A hA))) =
        r • normalizedInductionK0.{uF, uV} F T B
          (B.finiteLengthClass F.Carrier A hA)

/-- After ambient induction, a geometric piece on quasicuspidal data is
the original induced class or zero, according to its source refinement. -/
theorem inducedGeometricPiece_quasicuspidal
    {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))
    (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier))
      (hA : A.HasFiniteLength),
      IsLeviQuasicuspidal B A.representation →
      normalizedInductionK0.{uF, uV} F T C
          (geometricPieceK0.{uF, uV} F T B C w S R hS hR
            (B.finiteLengthClass F.Carrier A hA)) =
        if refinedParabolic F.Carrier B S = ⊤ then
          normalizedInductionK0.{uF, uV} F T B
            (B.finiteLengthClass F.Carrier A hA)
        else 0 := by
  let := T.topology
  intro A hA hqc
  classical
  have hpiece := LinearMap.congr_fun
    (normalizedInductionK0_comp_geometricPieceK0.{uF, uV}
      F T B C w S R hS hR) (B.finiteLengthClass F.Carrier A hA)
  change normalizedInductionK0 F T C
      (geometricPieceK0 F T B C w S R hS hR
        (B.finiteLengthClass F.Carrier A hA)) =
    normalizedInductionK0 F T B
      (normalizedRefinedInductionK0 F T B S
        (normalizedRefinedJacquetK0 F T B S
          (B.finiteLengthClass F.Carrier A hA))) at hpiece
  rw [hpiece]
  split_ifs with hfull
  · have hwhole : S = MinimalRefinedJacquet.wholeRefinement B :=
      eq_wholeRefinement_of_refinedParabolic_eq_top B S hfull
    subst S
    exact congrArg (normalizedInductionK0.{uF, uV} F T B)
      (LinearMap.congr_fun
        (refinedInductionJacquetK0_wholeRefinement.{uF, uV} F T B)
        (B.finiteLengthClass F.Carrier A hA))
  · rw [normalizedRefinedJacquetK0_quasicuspidal F T B S A hA hqc hfull,
      map_zero, map_zero]

/-- The existing natural-multiple theorem supplies the unchanged statement. -/
theorem quasicuspidalInductionTerms :
    QuasicuspidalInductionTermsStatement.{uF, uV} F T := by
  let := T.topology
  intro n hn B C A hA hqc
  exact QuasicuspidalCutSupport.inductionJacquetInduction_natural_multiple.{uF, uV}
    F T B C hn A hA hqc

end Langlands.Aubert
