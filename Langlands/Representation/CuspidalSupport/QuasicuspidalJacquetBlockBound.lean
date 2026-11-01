import Langlands.Representation.CuspidalSupport.QuasicuspidalJacquetVanishingProof
import Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
import Langlands.Representation.CuspidalSupport.JacquetSubquotientProof

/-! A block-count bound on the nonzero Jacquet modules of quasicuspidal induction. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric SmoothRep

universe uF uV

namespace JacquetBlockBound

variable {R : Type uF} [CommRing R] [Nontrivial R] {n : ℕ}
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- Inclusion of a conjugated source Levi in the target Levi sends each
source block into one target block. -/
theorem blockIndex_eq_of_conjugatedLevi_le
    (hw : (B.leviSubgroup R).map
      (MulAut.conj (permutation n R w)).toMonoidHom ≤ C.leviSubgroup R)
    {a b : Fin n} (hab : blockIndex B a = blockIndex B b) :
    blockIndex C (w a) = blockIndex C (w b) := by
  have hsource : permutation n R (Equiv.swap (w a) (w b)) ∈
      (B.leviSubgroup R).map
        (MulAut.conj (permutation n R w)).toMonoidHom :=
    (TotalConjugatingCount.mem_map_conj_iff B w _).mpr
      ((TotalConjugatingCount.swap_entries_vanish_iff
        (blockIndex B) w w.injective a b).mpr hab)
  exact (TotalConjugatingCount.swap_entries_vanish_iff
    (blockIndex C) id Function.injective_id (w a) (w b)).mp
      ((levi_mem_iff C _).mp (hw hsource))

/-- Such a Levi inclusion cannot give the target more blocks than the source. -/
theorem target_length_le_of_conjugatedLevi_le
    (hw : (B.leviSubgroup R).map
      (MulAut.conj (permutation n R w)).toMonoidHom ≤ C.leviSubgroup R) :
    C.length ≤ B.length := by
  have hlabel (x : Fin n) :
      blockIndex C (w x) = blockMap B C w (blockIndex B x) :=
    blockIndex_eq_of_conjugatedLevi_le B C w hw
      (blockIndex_index B (blockIndex B x) ⟨0, B.positive _⟩).symm
  have hsurj : Function.Surjective (blockMap B C w) := by
    intro j
    refine ⟨blockIndex B (w.symm (C.index j ⟨0, C.positive j⟩)), ?_⟩
    rw [← hlabel, Equiv.apply_symm_apply, blockIndex_index]
  simpa using Fintype.card_le_of_surjective (blockMap B C w) hsurj

end JacquetBlockBound

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n)

/-- No normalized Jacquet module at a shape with more than `B.length` blocks
has a nonzero actual carrier. -/
def HasJacquetBlockBound :
    letI := T.topology
    SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier) → Prop :=
  letI := T.topology
  fun π => ∀ C : BlockShape n, B.length < C.length →
    Subsingleton ((T.normalizedJacquetFunctor C).obj π)

/-- A shape with more blocks than `B` has no refinement conjugate to `B`. -/
theorem no_associated_refinement_of_length_gt (C : BlockShape n)
    (hBC : B.length < C.length) :
    ¬ ∃ (S : BlockRefinement C) (w : Equiv.Perm (Fin n)),
      (B.leviSubgroup F.Carrier).map
        (MulAut.conj (permutation n F.Carrier w)).toMonoidHom =
        (refinedLevi F.Carrier C S).map (C.leviEmbedding F.Carrier) := by
  rintro ⟨S, w, hw⟩
  have hincl : (B.leviSubgroup F.Carrier).map
      (MulAut.conj (permutation n F.Carrier w)).toMonoidHom ≤
      C.leviSubgroup F.Carrier := by
    rw [hw]
    exact Subgroup.map_le_range _ _
  exact (Nat.not_le_of_lt hBC)
    (JacquetBlockBound.target_length_le_of_conjugatedLevi_le B C w hincl)

/-- The geometric-filtration vanishing theorem kills every Jacquet module
with too many target blocks. -/
theorem quasicuspidal_induction_jacquet_subsingleton_of_length_gt (C : BlockShape n)
    (hBC : B.length < C.length) :
    letI := T.topology
    ∀ σ : SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier),
      IsLeviQuasicuspidal B σ.representation →
      Subsingleton ((T.normalizedJacquetFunctor C).obj
        ((T.normalizedParabolicInductionFunctor B).obj σ)) := by
  let := T.topology
  intro σ hqc
  exact quasicuspidalJacquetVanishing F T n B C σ hqc
    (no_associated_refinement_of_length_gt F B C hBC)

/-- Actual subquotients inherit an upper bound on nonzero Jacquet block counts. -/
theorem hasJacquetBlockBound_of_subquotient :
    letI := T.topology
    ∀ {A π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)},
      HasJacquetBlockBound F T B A → IsSubquotient π A →
      HasJacquetBlockBound F T B π := by
  let := T.topology
  intro A π hA hπ C hC
  let := hA C hC
  exact subsingleton_of_isSubquotient
    (normalizedJacquetSubquotient p F T n C A π hπ)

/-- Every actual subquotient of induction from quasicuspidal data satisfies
the source block bound. No finite-length hypothesis is needed. -/
theorem quasicuspidal_subquotient_hasJacquetBlockBound :
    letI := T.topology
    ∀ σ : SmoothRep.{0,uF,max uF uV} ℂ (B.Levi F.Carrier),
      IsLeviQuasicuspidal B σ.representation →
      ∀ π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier),
        IsSubquotient π ((T.normalizedParabolicInductionFunctor B).obj σ) →
        HasJacquetBlockBound F T B π := by
  let := T.topology
  intro σ hqc π hπ
  apply hasJacquetBlockBound_of_subquotient F T B ?_ hπ
  intro C hC
  exact quasicuspidal_induction_jacquet_subsingleton_of_length_gt F T B C hC σ hqc

end Langlands.CuspidalSupport
