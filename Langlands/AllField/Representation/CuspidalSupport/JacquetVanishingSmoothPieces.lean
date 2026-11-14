import Langlands.Representation.CuspidalSupport.JacquetVanishingSmoothPieces
import Langlands.AllField.Representation.Geometric.GeometricLemmaStatement
noncomputable section

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding geometricPieceInducingFunctor geometricPieceSmoothFunctor geometricPieceSmoothFunctor_obj_toRep geometricPieceSmoothFunctor_toRep
open Langlands.AllField.CuspidalSupport

open _root_.CategoryTheory
open Langlands.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllField.Geometric

universe uF uV

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- The actual smooth input to the last induction in a geometric piece. -/
def geometricPieceInducingFunctor {n : ℕ} (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F B C w = refinedLevi F B S)
    (hR : sourceLevi F C B w⁻¹ = refinedLevi F C R) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F) ⥤
      SmoothRep.{0, uF, uV} ℂ (refinedLevi F C R) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact T.normalizedRefinedJacquetFunctor B S ⋙
    subgroupEqualityFunctor _ _ hS.symm ⋙
    intersectionTransportFunctor F B C w ⋙
    subgroupEqualityFunctor _ _ hR

/-- Retain the actual smooth object before forgetting smoothness in a geometric piece. -/
def geometricPieceSmoothFunctor {n : ℕ} (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F B C w = refinedLevi F B S)
    (hR : sourceLevi F C B w⁻¹ = refinedLevi F C R) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (C.Levi F) := by
  letI := T.topology
  exact geometricPieceInducingFunctor F T B C w S R hS hR ⋙
    T.normalizedRefinedInductionFunctor C R

/-- Forgetting the constructed smoothness returns the exact geometric piece. -/
theorem geometricPieceSmoothFunctor_toRep {n : ℕ} (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F B C w = refinedLevi F B S)
    (hR : sourceLevi F C B w⁻¹ = refinedLevi F C R) :
    letI := T.topology
    geometricPieceSmoothFunctor.{uF, uV} F T B C w S R hS hR ⋙ SmoothRep.toRep =
      geometricPieceFunctor T B C w S R hS hR := by
  let := T.topology
  rfl

/-- The smooth representative has exactly the geometric piece's action and carrier. -/
theorem geometricPieceSmoothFunctor_obj_toRep {n : ℕ} (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F B C w = refinedLevi F B S)
    (hR : sourceLevi F C B w⁻¹ = refinedLevi F C R) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F),
      ((geometricPieceSmoothFunctor F T B C w S R hS hR).obj A).obj =
        (geometricPieceFunctor T B C w S R hS hR).obj A := by
  let := T.topology
  intro A
  exact congrArg (fun H => H.obj A)
    (geometricPieceSmoothFunctor_toRep F T B C w S R hS hR)

end Langlands.AllField.CuspidalSupport
