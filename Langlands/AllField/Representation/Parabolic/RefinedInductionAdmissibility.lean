import Langlands.Representation.Parabolic.RefinedInductionAdmissibility
import Langlands.AllField.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.AllField.Representation.Geometric.RefinementFunctorsSupplement
import Langlands.AllField.Representation.Jacquet.ParabolicSupplement
import Langlands.AllField.Representation.Parabolic.LeviInflationAdmissibilityProof
import Langlands.AllField.Representation.Parabolic.RefinementCompositionSupplement
/-! Admissibility of actual normalized induction inside a product Levi. -/

noncomputable section

namespace Langlands.AllField

universe uH uG

end Langlands.AllField

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding isCompact_integralRange parabolicQuotientCompact quotientMap_image_integralRange refinedParabolicQuotientCompact refinedQuotientMap_image_integralRange
open Langlands.AllField.Parabolic

open Langlands.GeneralLinear
open Langlands.Geometric

universe uF uV

section Local

variable {F : Type uF} [Field F] (T : LocalFieldData F)
  {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Every right coset of the actual refined parabolic meets the product of the
integral groups of the outer blocks. -/
theorem refinedQuotientMap_image_integralRange :
    letI := T.valuativeRel
    Induction.quotientMap (refinedParabolic F B S) ''
      (Set.univ.pi fun i =>
        (Iwasawa.integralRange (ValuativeRel.valuation F) (B.size i) :
          Set (GeneralLinear (B.size i) F))) = Set.univ := by
  let := T.valuativeRel
  refine Set.eq_univ_of_forall fun x => ?_
  induction x using Quotient.inductionOn with
  | h g =>
    choose k hk hup using fun i =>
      Iwasawa.exists_mul_upperTriangular (ValuativeRel.valuation F) (B.size i) (g i)
    refine ⟨fun i => (k i)⁻¹, fun i _ => inv_mem (hk i), Quotient.sound ?_⟩
    change QuotientGroup.rightRel _ (fun i => (k i)⁻¹) g
    rw [QuotientGroup.rightRel_apply, mem_refinedParabolic]
    intro i
    have h := (S i).mem_parabolic_of_isUpperTriangular _ (hup i)
    simpa only [Pi.mul_apply, Pi.inv_apply, inv_inv] using h

end Local

/-- The actual coset space of a refined parabolic in a product Levi is compact,
for every block shape and refinement, including empty blocks and rank zero. -/
theorem refinedParabolicQuotientCompact (F : Type uF) [Field F]
    (T : LocalFieldData F) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B) :
    letI := T.topology
    CompactSpace (Induction.LeftQuotient (refinedParabolic F B S)) := by
  let := T.topology
  let := T.valuativeRel
  refine ⟨?_⟩
  rw [← refinedQuotientMap_image_integralRange T B S]
  exact (isCompact_univ_pi fun i => isCompact_integralRange T (B.size i)).image
    continuous_quotient_mk'

end Langlands.AllField.Parabolic
