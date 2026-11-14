import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllFieldBZ.Representation.Geometric.GeometricLemmaStatement
import Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedJacquetFiltrationTheorem NonassociatedJacquetSubquotientsTheorem geometricPieceFunctor_subsingleton_of_proper_source nonassociatedJacquetSubquotients_rankZero normalizedRefinedInductionFunctor_subsingleton
open Langlands.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllFieldBZ.Geometric
open CategoryTheory
universe uF uV

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

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
    ∀ A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S),
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
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      IsLeviQuasicuspidal B A.representation →
      refinedParabolic F.Carrier B S ≠ ⊤ →
      Subsingleton ((Langlands.AllFieldBZ.Geometric.geometricPieceFunctor T B C w S R hS hR).obj A) := by
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
  let W := (intersectionTransportFunctor F.Carrier B C w).obj J'
  have hW : Subsingleton W := hJ'
  let := hW
  let W' := (subgroupEqualityFunctor _ _ hR).obj W
  have hW' : Subsingleton W' := subgroupEqualityFunctor_subsingleton _ _ _ W
  exact normalizedRefinedInductionFunctor_subsingleton F T C R W' hW'

end Langlands.AllFieldBZ.CuspidalSupport
