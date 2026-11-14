import Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers
import Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllField.Representation.Geometric.GeometricLemmaStatement
namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedJacquetFiltrationTheorem NonassociatedJacquetSubquotientsTheorem geometricPieceFunctor_subsingleton_of_proper_source nonassociatedJacquetSubquotients_rankZero normalizedRefinedInductionFunctor_subsingleton
open Langlands.AllField.CuspidalSupport

open _root_.CategoryTheory
open Langlands.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllField.Geometric

universe uF uV

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- The nonassociation hypothesis is impossible at rank zero. -/
theorem nonassociatedJacquetSubquotients_rankZero :
    NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T 0 := by
  let := T.topology
  intro B C ρ hρ hBC
  exact False.elim (hBC (levisAssociated_rankZero B C))

/-- Normalized refined induction of a zero representation is zero. -/
theorem normalizedRefinedInductionFunctor_subsingleton {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F B S),
      Subsingleton A → Subsingleton ((T.normalizedRefinedInductionFunctor B S).obj A) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A hA
  let := hA
  change Subsingleton (Induction.SmoothFunctions _ _)
  infer_instance

/-- A geometric piece vanishes when its source refinement is proper and
its inducing representation is quasicuspidal. -/
theorem geometricPieceFunctor_subsingleton_of_proper_source {n : ℕ}
    (B C : BlockShape n) (w : Equiv.Perm (Fin n))
    (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F B C w = refinedLevi F B S)
    (hR : sourceLevi F C B w⁻¹ = refinedLevi F C R) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F),
      IsLeviQuasicuspidal B A.representation →
      refinedParabolic F B S ≠ ⊤ →
      Subsingleton ((geometricPieceFunctor T B C w S R hS hR).obj A) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A hA hproper
  let J := (T.normalizedRefinedJacquetFunctor B S).obj A
  have hJ : Subsingleton J := hA S hproper
  let := hJ
  let J' := (subgroupEqualityFunctor _ _ hS.symm).obj J
  have hJ' : Subsingleton J' := subgroupEqualityFunctor_subsingleton _ _ _ J
  let := hJ'
  let W := (intersectionTransportFunctor F B C w).obj J'
  have hW : Subsingleton W := hJ'
  let := hW
  let W' := (subgroupEqualityFunctor _ _ hR).obj W
  have hW' : Subsingleton W' := subgroupEqualityFunctor_subsingleton _ _ _ W
  exact normalizedRefinedInductionFunctor_subsingleton F T C R W' hW'

end Langlands.AllField.CuspidalSupport
