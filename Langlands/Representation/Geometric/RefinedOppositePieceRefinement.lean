import Langlands.Representation.Geometric.RefinementUniqueness
import Langlands.Representation.Geometric.RefinedOppositePieceTransport

/-! Reconcile an arbitrary geometric-lemma source refinement with inner reversal. -/

noncomputable section

namespace Langlands.Geometric.RefinedOppositePieceTransport

open GeneralLinear CuspidalSupport ProductLeviDualOpposite
open OppositeCuspidalJacquetFiltration

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
  (C : BlockShape n) (x : Equiv.Perm (Fin n))
  (hx : ConjugatesLevi (F := F.Carrier) (B.flatten S) C x)
  (S' : BlockRefinement B) (R : BlockRefinement C.reverse)
  (hS : sourceLevi F.Carrier B C.reverse (reversedPiecePermutation B S C x) =
    refinedLevi F.Carrier B S')
  (hR : sourceLevi F.Carrier C.reverse B (reversedPiecePermutation B S C x)⁻¹ =
    refinedLevi F.Carrier C.reverse R)

/-- The whole-target piece comparison for any source refinement with the
actual geometric-lemma Levi intersection. The refinement is determined by
that intersection, rather than supplied as a prescribed reversal. -/
def chosenRefinementReversedWholeLeviGeometricPieceEquiv :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      Representation.Equiv
        ((((geometricPieceFunctor T B C.reverse (reversedPiecePermutation B S C x)
          S' R hS hR).obj A).ρ).comp (leviReverseEquiv C).toMonoidHom)
        (transport (B.flatten S) C x hx
          ((T.normalizedRefinedOppositeJacquet B S A.representation).comp
            (flattenedLeviEquiv F.Carrier B S).toMonoidHom)) := by
  have hy := conjugatesLevi_reversedPiece B S F.Carrier C x hx
  have hsource := sourceLevi_eq_refined_of_flattened_conjugates
    B C.reverse (reverseRefinement B S) (reversedPiecePermutation B S C x) hy
  have hS' : S' = reverseRefinement B S :=
    blockRefinement_eq_of_refinedLevi_eq B (hS.symm.trans hsource)
  subst S'
  exact reversedWholeLeviGeometricPieceEquiv B S T C x hx R hS hR

end Langlands.Geometric.RefinedOppositePieceTransport
