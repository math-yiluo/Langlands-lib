import Langlands.AllFieldBZ.Representation.CuspidalSupport.UniformJacquetVanishingStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetSubquotientProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetVanishingHelpers
import Langlands.AllFieldBZ.Representation.Geometric.GeometricLemmaProof
import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
import Langlands.Representation.Filtration.SingleSurvivingGrade
import Langlands.Representation.Geometric.RefinementSolomonCoefficients

/-! Proper source refinements force zero geometric-lemma factors. -/

namespace Langlands.AllFieldBZ.CuspidalSupport

open CategoryTheory Langlands.GeneralLinear Langlands.CuspidalSupport
open Langlands.Geometric (BlockRefinement refinedLevi refinedLevi_map_leviEmbedding)

universe uF uV

section Helpers

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

private theorem no_associated_refinement {n r : ℕ} (B C : BlockShape n)
    (hB : ∀ i, B.size i = r) (j : Fin C.length) (hj : ¬ r ∣ C.size j) :
    ¬ ∃ (S : BlockRefinement C) (w : Equiv.Perm (Fin n)),
      (B.leviSubgroup F.Carrier).map
        (MulAut.conj (permutation n F.Carrier w)).toMonoidHom =
        (refinedLevi F.Carrier C S).map (C.leviEmbedding F.Carrier) := by
  rintro ⟨S, w, hw⟩
  rw [refinedLevi_map_leviEmbedding] at hw
  have h : ConjugatesLevi (F := F.Carrier) B (C.flatten S) w := hw
  have hconst (k : Fin (C.flatten S).length) : (C.flatten S).size k = r := by
    obtain ⟨i, rfl⟩ := TotalConjugatingCount.blockMap_surjective h k
    exact (TotalConjugatingCount.size_blockMap h i).trans (hB i)
  have hinner (i : Fin (S j).length) : (S j).size i = r :=
    (C.flatten_size_flattenBlockEquiv S ⟨j, i⟩).symm.trans
      (hconst (C.flattenBlockEquiv S ⟨j, i⟩))
  refine hj ⟨(S j).length, ?_⟩
  calc
    C.size j = ∑ i, (S j).size i := (S j).sum_eq.symm
    _ = r * (S j).length := by simp [hinner, Nat.mul_comm]

set_option maxHeartbeats 1200000 in
private theorem jacquet_induced_zero {n : ℕ} (hn : 0 < n) (B C : BlockShape n)
    (hBC : ¬ ∃ (S : BlockRefinement C) (w : Equiv.Perm (Fin n)),
      (B.leviSubgroup F.Carrier).map
        (MulAut.conj (permutation n F.Carrier w)).toMonoidHom =
        (refinedLevi F.Carrier C S).map (C.leviEmbedding F.Carrier)) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      IsLeviQuasicuspidal B A.representation →
      Subsingleton ((T.normalizedJacquetFunctor C).obj
        ((T.normalizedParabolicInductionFunctor B).obj A)) := by
  let := T.topology
  intro A hA
  obtain ⟨S, R, hS, hR, m, e, a, s, hs⟩ :=
    Langlands.AllFieldBZ.Geometric.padicGeometricLemma.{uF, uV} F T n hn B C
  apply s.subsingleton_atObject A
  intro i
  obtain ⟨ei⟩ := hs i
  let w := e (a i)
  have hp := source_refinement_proper_of_no_associated_refinement B C hBC
    w.val (S w) (R w) (hS w) (hR w)
  have hz := geometricPieceFunctor_subsingleton_of_proper_source F T B C
    w.val (S w) (R w) (hS w).2.1 (hR w).2.1 A hA hp
  exact ⟨fun x y => (Representation.equivOfIso (ei.app A)).injective (hz.elim _ _)⟩

end Helpers

/-- Every target block size is divisible by the common inducing size
whenever a subquotient has a nonzero normalized Jacquet module. -/
theorem uniformJacquetVanishing (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) :
    UniformJacquetVanishingStatement.{uF, uV} F T := by
  let := T.topology
  intro n r B C hB j hj A hA I π hπ
  have hle : C.size j ≤ ∑ i, C.size i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (C.size i)) (Finset.mem_univ j)
  have hn : 0 < n := C.sum_eq ▸ lt_of_lt_of_le (C.positive j) hle
  let := jacquet_induced_zero T hn B C (no_associated_refinement (F := F) B C hB j hj) A hA
  exact subsingleton_of_isSubquotient (normalizedJacquetSubquotient F T n C I π hπ)

end Langlands.AllFieldBZ.CuspidalSupport
