import Langlands.AllFieldBZ.Representation.Geometric.FlattenedLevi
import Langlands.AllFieldBZ.Representation.Geometric.RefinementFunctors
import Langlands.AllFieldBZ.Representation.Parabolic.LeviInflationAdmissibilityProof
import Langlands.AllFieldBZ.Representation.Parabolic.QuotientCompactProof
import Langlands.Representation.Parabolic.RefinedInductionAdmissibility

/-!
# All-field port of `Langlands.Representation.Parabolic.RefinedInductionAdmissibility`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.RefinedInductionAdmissibility` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ
universe uH uG

end Langlands.AllFieldBZ
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding LeviInflationAdmissibilityClause ParabolicQuotientCompactClause UnipotentFiniteContainmentClause isAdmissible_refinedInflation_iff isCompact_integralRange isOpenMap_refinedLeviProjection leviInflationAdmissibility normalizedRefinedInductionAdmissibility parabolicQuotientCompact quotientMap_image_integralRange refinedParabolicQuotientCompact refinedQuotientMap_image_integralRange
open Langlands.GeneralLinear
open Langlands.Geometric
universe uF uV

section Local
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The actual refined Levi projection is an open map. -/
theorem isOpenMap_refinedLeviProjection :
    letI := T.topology
    IsOpenMap (refinedLeviProjection F.Carrier B S) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.leviTopologicalGroup B
  exact isOpenMap_of_continuous_rightInverse (refinedLeviProjection F.Carrier B S)
    (refinedLeviSection F.Carrier B S) (refinedLeviSectionContinuous F.Carrier B S).continuous
    (refinedLeviProjection_section F.Carrier B S)

/-- Admissibility is preserved and reflected by inflation through the actual
refined Levi projection. -/
theorem isAdmissible_refinedInflation_iff {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (refinedLevi F.Carrier B S) V) :
    letI := T.topology
    IsAdmissible (σ.comp (refinedLeviProjection F.Carrier B S)) ↔ IsAdmissible σ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact isAdmissible_comp_iff_of_open_surjective σ (refinedLeviProjection F.Carrier B S)
    (refinedLeviProjectionContinuous F.Carrier B S).continuous
    (isOpenMap_refinedLeviProjection T B S)
    (fun m => ⟨refinedLeviSection F.Carrier B S m, refinedLeviProjection_section F.Carrier B S m⟩)

/-- Every right coset of the actual refined parabolic meets the product of the
integral groups of the outer blocks. -/
theorem refinedQuotientMap_image_integralRange :
    letI := T.valuativeRel
    Induction.quotientMap (refinedParabolic F.Carrier B S) ''
      (Set.univ.pi fun i =>
        (Iwasawa.integralRange (ValuativeRel.valuation F.Carrier) (B.size i) :
          Set (GeneralLinear (B.size i) F.Carrier))) = Set.univ := by
  let := T.valuativeRel
  refine Set.eq_univ_of_forall fun x => ?_
  induction x using Quotient.inductionOn with
  | h g =>
    choose k hk hup using fun i =>
      Iwasawa.exists_mul_upperTriangular (ValuativeRel.valuation F.Carrier) (B.size i) (g i)
    refine ⟨fun i => (k i)⁻¹, fun i _ => inv_mem (hk i), Quotient.sound ?_⟩
    change QuotientGroup.rightRel _ (fun i => (k i)⁻¹) g
    rw [QuotientGroup.rightRel_apply, mem_refinedParabolic]
    intro i
    have h := (S i).mem_parabolic_of_isUpperTriangular _ (hup i)
    simpa only [Pi.mul_apply, Pi.inv_apply, inv_inv] using h

end Local
/-- The actual coset space of a refined parabolic in a product Levi is compact,
for every block shape and refinement, including empty blocks and rank zero. -/
theorem refinedParabolicQuotientCompact (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B) :
    letI := T.topology
    CompactSpace (Induction.LeftQuotient (refinedParabolic F.Carrier B S)) := by
  let := T.topology
  let := T.valuativeRel
  refine ⟨?_⟩
  rw [← refinedQuotientMap_image_integralRange T B S]
  exact (isCompact_univ_pi fun i => isCompact_integralRange T (B.size i)).image
    continuous_quotient_mk'

/-- Actual normalized refined induction preserves admissibility. -/
theorem normalizedRefinedInductionAdmissibility (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (refinedLevi F.Carrier B S) V) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    IsAdmissible σ → IsAdmissible (T.normalizedRefinedInduced B S σ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.leviTopologicalGroup B
  intro hσ
  have hTwisted : IsAdmissible (twist (T.refinedParabolicHalfModulus B S)
      (σ.comp (refinedLeviProjection F.Carrier B S))) :=
    (isAdmissible_twist_iff _ _ (T.isOpen_ker_refinedParabolicHalfModulus B S)).mpr
      ((isAdmissible_refinedInflation_iff T B S σ).mpr hσ)
  have := refinedParabolicQuotientCompact F T B S
  exact Induction.smoothInduced_isAdmissible_of_compactSpace _ _ hTwisted

end Langlands.AllFieldBZ.Parabolic
