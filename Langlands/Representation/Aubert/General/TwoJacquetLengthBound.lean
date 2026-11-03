import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Aubert.General.LengthTwoExtraction
import Langlands.Representation.Filtration.ExactFamilyLengthProof

/-! # Composition length detected by two actual Jacquet modules -/

noncomputable section

namespace Langlands.Aubert.General

universe uG uV

open CategoryTheory SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U Q L V : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U)
  (hO : IsSemidirectDecomposition Q L V) (hV : IsClosed (V : Set G))
  (hVc : Jacquet.Localization.IsLimitOfCompactSubgroups V)
  (A : SmoothRep.{0, uG, uV} ℂ G)
  (hJac : ((jacquetFunctor.{uG, uV} h hU).obj A).IsIrreducible)
  (hJacO : ((jacquetFunctor.{uG, uV} hO hV).obj A).IsIrreducible)
  (hdetect : ∀ D : SmoothRep.{0, uG, uV} ℂ G,
    D.IsIrreducible → IsSubquotient D A →
    Nontrivial ((jacquetFunctor.{uG, uV} h hU).obj D) ∨
      Nontrivial ((jacquetFunctor.{uG, uV} hO hV).obj D))

include hUc hVc hJac hJacO hdetect

/-- Two simple actual Jacquet images and joint detection of irreducible
subquotients give an actual composition series of length at most two. -/
theorem two_jacquet_compositionLengthAtMost_two :
    HasCompositionLengthAtMost A.obj 2 := by
  let H : Bool → Type uG := fun b => if b then L else M
  let : ∀ b, Group (H b) := fun b => by
    cases b <;> dsimp [H] <;> infer_instance
  let : ∀ b, TopologicalSpace (H b) := fun b => by
    cases b <;> dsimp [H] <;> infer_instance
  let F : ∀ b, SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uG, uV} ℂ (H b) :=
    fun b => by
      cases b
      · exact jacquetFunctor h hU
      · exact jacquetFunctor hO hV
  have hF : ∀ b, Derivative.Mirabolic.MapsShortExactIntertwiners (F b) := by
    intro b
    cases b
    · intro B C D i q hi hq hex
      have hs := jacquetFunctor_map_isShortExact h hU hUc i q ⟨hi, hq, hex⟩
      exact ⟨hs.1, hs.2.2, hs.2.1⟩
    · intro B C D i q hi hq hex
      have hs := jacquetFunctor_map_isShortExact hO hV hVc i q ⟨hi, hq, hex⟩
      exact ⟨hs.1, hs.2.2, hs.2.1⟩
  have hb : ∀ b, repLength ((F b).obj A).representation ≤ (1 : ℕ∞) := by
    intro b
    cases b
    · exact (repLength_eq_one_iff.mpr hJac).le
    · exact (repLength_eq_one_iff.mpr hJacO).le
  have hd : ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      D.IsIrreducible → IsSubquotient D A → ∃ b, Nontrivial ((F b).obj D) := by
    intro D hD hDA
    rcases hdetect D hD hDA with hD0 | hD1
    · exact ⟨false, hD0⟩
    · exact ⟨true, hD1⟩
  simpa using exactFamilyLengthBound Bool G H F hF A (fun _ => 1) hb hd

/-- A chosen actual invariant-subspace filtration with at most two simple
successive quotients, rather than only an assertion of finite length. -/
def twoJacquetCompositionSeries :
    Σ n : Fin 3, {s : ObjectRepFiltration A.obj n.val // s.HasSimpleFactors} := by
  let hb := two_jacquet_compositionLengthAtMost_two h hU hUc hO hV hVc A
    hJac hJacO hdetect
  let n := Classical.choose hb
  have hn : n ≤ 2 := (Classical.choose_spec hb).1
  have hs : HasCompositionSeriesLength A.obj n := (Classical.choose_spec hb).2
  exact ⟨⟨n, Nat.lt_succ_of_le hn⟩, Classical.choose hs, Classical.choose_spec hs⟩

/-- The corresponding bound on the actual group-algebra composition length. -/
theorem two_jacquet_repLength_le_two :
    repLength A.representation ≤ 2 := by
  obtain ⟨n, hn, s, hs⟩ := two_jacquet_compositionLengthAtMost_two h hU hUc hO hV hVc A
    hJac hJacO hdetect
  change repLength A.obj.ρ ≤ 2
  rw [repLength_eq_of_hasSimpleFactors s hs]
  exact_mod_cast hn

/-- Every nonzero proper invariant subspace and its actual quotient are
irreducible under the displayed two-Jacquet hypotheses. -/
theorem two_jacquet_proper_subrepresentation_irreducible
    (S : Subrepresentation A.representation) (hS0 : S ≠ ⊥) (hS1 : S ≠ ⊤) :
    (subrepresentation A S).IsIrreducible ∧ (quotient A S).IsIrreducible := by
  obtain ⟨hs, hq⟩ := subrepresentation_quotient_length_eq_one A
    (two_jacquet_repLength_le_two h hU hUc hO hV hVc A hJac hJacO hdetect) S hS0 hS1
  exact ⟨repLength_eq_one_iff.mp hs, repLength_eq_one_iff.mp hq⟩

end Langlands.Aubert.General
