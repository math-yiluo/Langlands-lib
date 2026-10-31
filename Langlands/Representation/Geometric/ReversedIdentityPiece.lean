import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
import Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof
import Langlands.Representation.CuspidalSupport.LeviAssociation

/-! The actual inverse-reversal geometric piece after target Levi relabelling. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CuspidalSupport CategoryTheory
open OppositeCuspidalJacquetFiltration

universe uF uV

private theorem reversalLeviConjugation {F : Type uF} [Field F]
    {n : ℕ} (B : BlockShape n) :
    leviConjugation B.reverse B B.reversePermutation (conjugatesLevi_reverse (F := F) B) =
      (leviReverseEquiv (R := F) B).symm := by
  apply MulEquiv.ext
  intro m
  apply B.leviEmbedding_injective F
  rw [leviConjugation_embedding, ← reverseMatrix_mul_leviEmbedding B
    ((leviReverseEquiv (R := F) B).symm m), MulEquiv.apply_symm_apply]
  rfl

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}

set_option maxHeartbeats 1400000 in
/-- The published full-refinement maps identify any whole-Levi-conjugating
piece on a smooth source with actual whole-Levi transport, using only the
actual source and target Levi equalities. -/
private def wholeConjugatingPieceEquiv (B C : BlockShape n) (w : Equiv.Perm (Fin n))
    (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R)
    (hw : ConjugatesLevi (F := F.Carrier) B C w) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      ((geometricPieceFunctor T B C w S R hS hR).obj A).ρ.Equiv
        (transport B C w hw A.representation) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A
  have hfullS : refinedLevi F.Carrier B S = ⊤ :=
    hS.symm.trans (sourceLevi_eq_top_of_conjugates B C w hw)
  have hfullR : refinedLevi F.Carrier C R = ⊤ :=
    hR.symm.trans (targetLevi_eq_top_of_conjugates B C w hw)
  let J := (T.normalizedRefinedJacquetFunctor B S).obj A
  let eJ : J.representation.Equiv
      (A.representation.comp (refinedLevi F.Carrier B S).subtype) :=
    fullRefinedJacquetEquiv T B S hfullS A.representation
  let J' := (subgroupEqualityFunctor _ _ hS.symm).obj J
  let eJ' : J'.representation.Equiv
      (A.representation.comp (sourceLevi F.Carrier B C w).subtype) :=
    subgroupEqualityEquiv _ _ hS.symm J A.representation eJ
  let τ := transport B C w hw A.representation
  let Q := (intersectionTransportFunctor F.Carrier B C w).obj J'
  let eQ : Q.representation.Equiv
      (τ.comp (sourceLevi F.Carrier C B w⁻¹).subtype) :=
    intersectionTransportFullEquiv B C w hw J'.representation A.representation eJ'
  let Q' := (subgroupEqualityFunctor _ _ hR).obj Q
  let eQ' : Q'.representation.Equiv
      (τ.comp (refinedLevi F.Carrier C R).subtype) :=
    subgroupEqualityEquiv _ _ hR Q τ eQ
  have hτ : IsSmooth τ := isSmooth_transport B C w hw A.isSmooth
  change (T.normalizedRefinedInduced C R Q'.representation).Equiv τ
  exact fullRefinedInductionEquiv T C R hfullR Q'.representation τ eQ' hτ

set_option maxHeartbeats 1600000 in
/-- After actual reversed-label pullback, the inverse block-reversal piece is
the original smooth source. Arbitrary actual intersection Levi refinements
and equality witnesses are retained, with no cuspidality or rank premise. -/
def reversedIdentityGeometricPieceEquiv (B : BlockShape n)
    (S : BlockRefinement B) (R : BlockRefinement B.reverse)
    (hS : sourceLevi F.Carrier B B.reverse B.reversePermutation.symm =
      refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier B.reverse B B.reversePermutation.symm⁻¹ =
      refinedLevi F.Carrier B.reverse R) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      Representation.Equiv
        ((((geometricPieceFunctor T B B.reverse B.reversePermutation.symm S R hS hR).obj A).ρ).comp
          (leviReverseEquiv B).toMonoidHom) A.representation := by
  let := T.topology
  intro A
  have hw : ConjugatesLevi (F := F.Carrier) B B.reverse B.reversePermutation.symm :=
    conjugatesLevi_inv (conjugatesLevi_reverse B)
  have e := wholeConjugatingPieceEquiv T B B.reverse B.reversePermutation.symm S R hS hR hw A
  have ht : transport B B.reverse B.reversePermutation.symm hw A.representation =
      A.representation.comp (leviReverseEquiv B).symm.toMonoidHom := by
    change transport B B.reverse B.reversePermutation⁻¹
      (conjugatesLevi_inv (conjugatesLevi_reverse B)) A.representation = _
    rw [transport_inv (conjugatesLevi_reverse B), reversalLeviConjugation]
  rw [ht] at e
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro m
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    using e.isIntertwining' (leviReverseEquiv B m)

end Langlands.Geometric
