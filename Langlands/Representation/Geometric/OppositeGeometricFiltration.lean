import Langlands.Representation.Geometric.OppositeRefinedFiltrationGraded
import Langlands.Representation.Geometric.GeometricLemmaStatement

/-! An objectwise composed opposite filtration extracted from the upper
geometric lemma, conditional on that published proposition. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CategoryTheory OppositeCuspidalJacquetFiltration

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (S : BlockRefinement C)

/-- Actual filtration data obtained by applying the reversed upper geometric
filtration to one smooth inducing representation and then taking the refined
opposite quotient. The upper geometric lemma is needed to construct this data. -/
structure ComposedOppositeGeometricFiltrationData
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)) where
  sourceRefinement : MinimalRepresentatives B C.reverse → BlockRefinement B
  targetRefinement : MinimalRepresentatives B C.reverse → BlockRefinement C.reverse
  sourceIntersection : ∀ w, IsIntersectionRefinement (F := F.Carrier)
    B C.reverse w.val (sourceRefinement w)
  targetIntersection : ∀ w, IsIntersectionRefinement (F := F.Carrier)
    C.reverse B w.val⁻¹ (targetRefinement w)
  length : ℕ
  enumeration : Fin length ≃ MinimalRepresentatives B C.reverse
  filtration : letI := T.topology
    ObjectRepFiltration
    (Rep.of (T.normalizedComposedOppositeJacquet C S
      (CuspidalJacquetMultiplicity.induced T B (Rep.of A.representation)).ρ)) length
  gradeEquiv : letI := T.topology
    ∀ i, Nonempty (Representation.Equiv
    ((filtration.gradedRepresentation i).ρ)
    (T.normalizedRefinedOppositeJacquet C S
      ((((geometricPieceFunctor T B C.reverse (enumeration i).val
        (sourceRefinement (enumeration i)) (targetRefinement (enumeration i))
        (sourceIntersection (enumeration i)).2.1
        (targetIntersection (enumeration i)).2.1).obj A).ρ).comp
          (leviReverseEquiv C).toMonoidHom)))

set_option maxHeartbeats 1200000 in
/-- The published upper geometric-lemma proposition, when supplied, constructs
the actual composed opposite filtration and all its same-index grade
comparisons. No opposite geometric-lemma proposition is assumed. -/
def composedOppositeGeometricFiltrationOfUpper
    (hupper : GeometricLemmaTheorem.{uF, uV} T B C.reverse)
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)) :
    ComposedOppositeGeometricFiltrationData T B C S A := by
  letI := T.topology
  apply Classical.choice
  obtain ⟨P, Q, hP, hQ, m, e, δ, f, hf⟩ := hupper
  let I := CuspidalJacquetMultiplicity.induced T B (Rep.of A.representation)
  let s : ObjectRepFiltration (Rep.of (T.normalizedJacquet C.reverse I.ρ)) m :=
    ObjectRepFiltration.ofSubrepresentations (fun k => (f.step k).obj A)
      (f.monotone A) (f.zero A) (f.top A)
  refine ⟨⟨P, Q, hP, hQ, m, δ.trans e,
    composedOppositeFiltrationOfReverse T C I S s, ?_⟩⟩
  intro i
  obtain ⟨ψ⟩ := hf i
  let g : (s.gradedRepresentation i).ρ.Equiv
      ((geometricPieceFunctor T B C.reverse (e (δ i)).val
        (P (e (δ i))) (Q (e (δ i)))
        (hP (e (δ i))).2.1 (hQ (e (δ i))).2.1).obj A).ρ :=
    Representation.equivOfIso (ψ.app A)
  exact ⟨composedOppositeFiltrationOfReverseGradeCongr T C I S s i _ g
    (T.isSmooth_normalizedParabolicInduced B A.representation)⟩

end Langlands.Geometric
