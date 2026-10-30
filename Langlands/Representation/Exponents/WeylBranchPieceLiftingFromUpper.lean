import Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
import Langlands.Representation.Geometric.RefinedOppositePieceMinimal
import Langlands.Representation.Geometric.RefinedOppositePieceRefinement

/-! Whole opposite-piece occurrence from the upper geometric lemma. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric CuspidalSupport
open RelativeJacquetMultiplicity WeylBranchPieces
open OppositeCuspidalJacquetFiltration Geometric.RefinedOppositePieceTransport

universe uF uV

set_option maxHeartbeats 400000 in
/-- The fixed transported whole opposite piece is a subquotient once the
upper geometric lemma at the reversed target has been proved. -/
theorem wholeOppositePiece_isSubquotient_of_upper
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
    (hupper : GeometricLemmaTheorem.{uF, uV} T B C.reverse)
    (S : BlockRefinement B) (x : Equiv.Perm (Fin n))
    (hmin : IsMinimalRepresentative B C x)
    (hx : ConjugatesLevi (F := F.Carrier) (B.flatten S) C x) :
    letI := T.topology
    ∀ (V : Rep.{uV} ℂ (B.Levi F.Carrier)), IsSmooth V.ρ →
      IsSubquotient
        (CuspidalJacquetMultiplicity.oppositeJacquet T C
          (CuspidalJacquetMultiplicity.induced T B V)).ρ
        (transport (B.flatten S) C x hx
          ((innerJacquet T B S V).ρ.comp
            (flattenedLeviEquiv F.Carrier B S).toMonoidHom)) := by
  let := T.topology
  intro V hV
  let A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) :=
    SmoothRep.of V.ρ hV
  obtain ⟨P, Q, hP, hQ, m, e, hglued⟩ := hupper
  let piece (w : MinimalRepresentatives B C.reverse) :=
    geometricPieceFunctor.{uF, uV} T B C.reverse w.val (P w) (Q w)
      (hP w).2.1 (hQ w).2.1
  have hglued' : IsGluedFrom (jacquetInductionFunctor T B C.reverse)
      (fun i => piece (e i)) := hglued
  let y := reversedPieceMinimalRepresentative B S hmin hx
  have hp := WeylBranchPieces.IsGluedFrom.isSubquotient_piece hglued' A (e.symm y)
  rw [e.apply_symm_apply] at hp
  have hp' := hp.comp (leviReverseEquiv (R := F.Carrier) C).toMonoidHom
  let ePiece := chosenRefinementReversedWholeLeviGeometricPieceEquiv T B S C x hx
    (P y) (Q y) (hP y).2.1 (hQ y).2.1 A
  dsimp only [piece, y, reversedPieceMinimalRepresentative] at hp'
  have hp'' : IsSubquotient
      (((jacquetInductionFunctor T B C.reverse).obj A).ρ.comp
        (leviReverseEquiv (R := F.Carrier) C).toMonoidHom)
      (transport (B.flatten S) C x hx
        ((T.normalizedRefinedOppositeJacquet B S A.representation).comp
          (flattenedLeviEquiv F.Carrier B S).toMonoidHom)) :=
    by with_reducible exact IsSubquotient.of_equiv_right hp' ePiece
  let eAmbient := oppositeJacquetReverseEquiv T C
    (CuspidalJacquetMultiplicity.induced T B V)
  exact IsSubquotient.of_equiv_left eAmbient.symm hp''

/-- Actual subrepresentation and surjective quotient map for the chosen
whole opposite piece, constructed from the upper geometric lemma. -/
def wholeOppositePieceSubquotientWitness
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
    (hupper : GeometricLemmaTheorem.{uF, uV} T B C.reverse)
    (S : BlockRefinement B) (x : Equiv.Perm (Fin n))
    (hmin : IsMinimalRepresentative B C x)
    (hx : ConjugatesLevi (F := F.Carrier) (B.flatten S) C x) :
    letI := T.topology
    ∀ (V : Rep.{uV} ℂ (B.Levi F.Carrier)), IsSmooth V.ρ →
      Σ U : Subrepresentation
          (CuspidalJacquetMultiplicity.oppositeJacquet T C
            (CuspidalJacquetMultiplicity.induced T B V)).ρ,
        {q : U.toRepresentation.IntertwiningMap
          (transport (B.flatten S) C x hx
            ((innerJacquet T B S V).ρ.comp
              (flattenedLeviEquiv F.Carrier B S).toMonoidHom)) //
          Function.Surjective q} := by
  let := T.topology
  intro V hV
  have h := wholeOppositePiece_isSubquotient_of_upper T B C hupper S x hmin hx V hV
  exact ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
    Classical.choose_spec (Classical.choose_spec h)⟩

/-- All fixed whole opposite pieces lift if the general upper geometric
lemma is available at the same independent universes. -/
theorem glGeometricPieceLifting_of_upper
    (hupper : PadicGeometricLemmaTheorem.{uF, uV}) :
    GLGeometricPieceLiftingStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n hn B C S x hmin hx V hV
  exact wholeOppositePiece_isSubquotient_of_upper T B C
    (hupper p F T n hn B C.reverse) S x hmin hx V hV

end Langlands
