import Langlands.Representation.CuspidalSupport.ProperInductionProof
import Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Representation.CuspidalSupport.CuspidalTensorStatement
import Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllField.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof
import Langlands.AllField.Representation.CuspidalSupport.ProperInductionMaps
import Langlands.AllField.Representation.CuspidalSupport.ProperInductionStatement
import Langlands.AllField.Representation.Geometric.GeometricLemmaStatement
/-! Proper normalized refined induction has no nonzero quasicuspidal subquotients. -/

noncomputable section

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedJacquetFiltrationTheorem GLCuspidalTensorStatement NonassociatedJacquetSubquotientsTheorem PadicProperRefinedInductionTheorem ProperRefinedInductionTheorem determinantUnitInclusion determinantUnitRestriction determinantUnitSubgroup induced_quasicuspidal_subrepresentation_subsingleton leviHarishChandraTheorem leviQuasicuspidalDecomposition levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup padicProperRefinedInduction
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllField.Geometric

universe uF uV

/-- BZ77 section 2.4(d), in the full subquotient form given by section 2.4(a). -/
theorem padicProperRefinedInduction :
    PadicProperRefinedInductionTheorem.{uF, uV} := by
  intro F _ T n hn B
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro S hS A D hD hDc
  let I := (T.normalizedRefinedInductionFunctor B S).obj A
  obtain ⟨U, Q, hcompl, hU, hQ⟩ :=
    leviQuasicuspidalDecomposition.{uF, max uF uV} F T B I
  let : Subsingleton (SmoothRep.subrepresentation I U) :=
    induced_quasicuspidal_subrepresentation_subsingleton T B S hS A U hU
  let e := complementIsoOfSubsingleton B I U Q hcompl
  exact hQ D (SmoothRep.IsSubquotient.of_iso_right hD e) hDc

end Langlands.AllField.CuspidalSupport
