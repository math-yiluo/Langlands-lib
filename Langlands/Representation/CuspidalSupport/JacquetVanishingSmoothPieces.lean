import Langlands.Representation.Geometric.GeometricLemmaStatement

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual smooth input to the last induction in a geometric piece. -/
def geometricPieceInducingFunctor {n : ℕ} (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier C R) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact T.normalizedRefinedJacquetFunctor B S ⋙
    subgroupEqualityFunctor _ _ hS.symm ⋙
    intersectionTransportFunctor F.Carrier B C w ⋙
    subgroupEqualityFunctor _ _ hR

/-- Retain the actual smooth object before forgetting smoothness in a geometric piece. -/
def geometricPieceSmoothFunctor {n : ℕ} (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (C.Levi F.Carrier) := by
  letI := T.topology
  exact geometricPieceInducingFunctor F T B C w S R hS hR ⋙
    T.normalizedRefinedInductionFunctor C R

/-- Forgetting the constructed smoothness returns the exact geometric piece. -/
theorem geometricPieceSmoothFunctor_toRep {n : ℕ} (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R) :
    letI := T.topology
    geometricPieceSmoothFunctor.{uF, uV} F T B C w S R hS hR ⋙ SmoothRep.toRep =
      geometricPieceFunctor T B C w S R hS hR := by
  let := T.topology
  rfl

/-- The smooth representative has exactly the geometric piece's action and carrier. -/
theorem geometricPieceSmoothFunctor_obj_toRep {n : ℕ} (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      ((geometricPieceSmoothFunctor F T B C w S R hS hR).obj A).obj =
        (geometricPieceFunctor T B C w S R hS hR).obj A := by
  let := T.topology
  intro A
  exact congrArg (fun H => H.obj A)
    (geometricPieceSmoothFunctor_toRep F T B C w S R hS hR)

end Langlands.CuspidalSupport
