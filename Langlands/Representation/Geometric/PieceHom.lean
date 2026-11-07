import Langlands.Representation.Geometric.GeometricLemmaProof
import Langlands.Combinatorics.FiniteOccurrenceMatching
import Langlands.Representation.CuspidalSupport.AssociationForwardHomSupport
import Langlands.Representation.CuspidalSupport.ConstituentProof
import Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof
import Langlands.Representation.Classification.FiniteLengthProof

/-! A nonzero map to a cuspidally induced representation from one geometric piece. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CuspidalSupport CategoryTheory

universe uF uV uW

/-- Matching occurrences in a weakly sorted target gives a minimal representative
when the ranking is strictly increasing inside every source block and the target
blocks have size one. Repeated target values are allowed. -/
theorem exists_minimal_matching_of_sorted
    {n : ℕ} {α β : Type*} [LinearOrder β]
    (B C : BlockShape n) (hC : ∀ j, C.size j = 1)
    (source target : Fin n → α) (ranking : α → β)
    (hcontent : (List.ofFn source : Multiset α) = List.ofFn target)
    (hsource : ∀ j, StrictMono (fun a => ranking (source (B.index j a))))
    (htarget : Monotone (fun i => ranking (target i))) :
    ∃ w : MinimalRepresentatives B C, ∀ i, source i = target (w.val i) := by
  obtain ⟨w, hw⟩ := Langlands.Combinatorics.exists_equiv_of_ofFn_multiset_eq
    source target hcontent
  refine ⟨⟨w, ?_, ?_⟩, hw⟩
  · intro j a b hab
    apply htarget.reflect_lt
    rw [← hw _, ← hw _]
    exact hsource j hab
  · intro j
    have : Subsingleton (Fin (C.size j)) := by rw [hC j]; infer_instance
    exact Subsingleton.strictMono _

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

set_option maxHeartbeats 1000000 in
/-- A single geometric piece isomorphic to irreducible cuspidal target data
gives a nonzero map of normalized inductions. -/
theorem exists_ne_zero_to_induced_of_piece
    {n : ℕ} (hn : 0 < n) (B C : BlockShape n)
    (σ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
    (τ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier))
    (hσ : letI := T.topology; σ.IsAdmissible)
    (hτ : letI := T.topology; τ.IsIrreducible)
    (hτc : letI := T.topology; IsLeviCuspidal C τ.representation)
    (w : MinimalRepresentatives B C)
    (hpiece : letI := T.topology;
      ∀ (S : BlockRefinement B) (R : BlockRefinement C)
        (hS : IsIntersectionRefinement (F := F.Carrier) B C w.val S)
        (hR : IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ R),
        Nonempty (((geometricPieceFunctor T B C w.val S R hS.2.1 hR.2.1).obj σ).ρ.Equiv
          τ.representation)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∃ f : (T.normalizedParabolicInduced B σ.representation).IntertwiningMap
        (T.normalizedParabolicInduced C τ.representation), f ≠ 0 := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  obtain ⟨S, R, hS, hR, M, e, order, s, hs⟩ :=
    padicGeometricLemma.{uF, uV} p F T n hn B C
  let enum : Fin M ≃ MinimalRepresentatives B C := order.trans e
  obtain ⟨i, rfl⟩ := enum.surjective w
  let evaluated := objectFiltrationAt s σ
  obtain ⟨g⟩ := hs i
  obtain ⟨h⟩ := hpiece (S (enum i)) (R (enum i)) (hS _) (hR _)
  have hA : ((T.normalizedJacquetFunctor C).obj
      ((T.normalizedParabolicInductionFunctor B).obj σ)).IsAdmissible :=
    FiniteLengthAssembly.isAdmissible_normalizedJacquet T C _
      (Parabolic.normalizedInductionAdmissibility F T B _ _ hσ)
  exact exists_ne_zero_of_gradedRepresentation_equiv T B C
    (leviCuspidalConstituentTheorem.{uF, max uF uV} F T C)
    σ τ hτ hτc hA M evaluated i ⟨(Representation.equivOfIso (g.app σ)).trans h⟩

/-- A chosen nonzero induction map supplied by the specified cuspidal geometric piece. -/
def nonzeroInductionMapOfPiece
    {n : ℕ} (hn : 0 < n) (B C : BlockShape n)
    (σ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
    (τ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier))
    (hσ : letI := T.topology; σ.IsAdmissible)
    (hτ : letI := T.topology; τ.IsIrreducible)
    (hτc : letI := T.topology; IsLeviCuspidal C τ.representation)
    (w : MinimalRepresentatives B C)
    (hpiece : letI := T.topology;
      ∀ (S : BlockRefinement B) (R : BlockRefinement C)
        (hS : IsIntersectionRefinement (F := F.Carrier) B C w.val S)
        (hR : IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ R),
        Nonempty (((geometricPieceFunctor T B C w.val S R hS.2.1 hR.2.1).obj σ).ρ.Equiv
          τ.representation)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    { f : (T.normalizedParabolicInduced B σ.representation).IntertwiningMap
        (T.normalizedParabolicInduced C τ.representation) // f ≠ 0 } := by
  let h := exists_ne_zero_to_induced_of_piece F T hn B C σ τ hσ hτ hτc w hpiece
  exact ⟨h.choose, h.choose_spec⟩

end Langlands.Geometric
