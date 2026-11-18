import Langlands.LinearAlgebra.FiniteCartanLeafClassification
import Mathlib.Logic.Equiv.Option

/-! # Classification by deletion of a leaf -/

universe u

open Matrix SimpleGraph

namespace Langlands.LinearAlgebra.FiniteCartanMatrix

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℤ}

theorem classification_from_leaf_numbering
    (hM : M.IsFiniteCartan) (v : ι) (hv : (diagram M).degree v = 1)
    {n : ℕ} (N : Matrix (Fin n) (Fin n) ℤ)
    (e : {i : ι // i ≠ v} ≃ Fin n)
    (he : ∀ i j : {i : ι // i ≠ v}, M i j = N (e i) (e j))
    (hclass : ∀ (k : Fin n) (a b : ℤ),
      (leafExtension N k a b).IsFiniteCartan → a < 0 →
        HasIrreducibleCartanType (leafExtension N k a b)) :
    HasIrreducibleCartanType M := by
  classical
  obtain ⟨w, hw, hu⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
  let w' : {i : ι // i ≠ v} := ⟨w, hw.ne.symm⟩
  let k := e w'
  let a := M w v
  let b := M v w
  let f : Fin (n + 1) ≃ ι :=
    ((finSuccEquiv' (Fin.last n)).trans (Equiv.optionCongr e.symm)).trans
      (Equiv.optionSubtypeNe v)
  have flast : f (Fin.last n) = v := by
    simp [f, finSuccEquiv'_at, Equiv.optionCongr]
  have fold (i : Fin n) : f i.castSucc = (e.symm i).val := by
    simp [f, finSuccEquiv'_below (Fin.castSucc_lt_last i), Equiv.optionCongr]
  have hrow (i : {j : ι // j ≠ v}) : M v i = if e i = k then b else 0 := by
    by_cases hi : e i = k
    · have heq : i = w' := e.injective hi
      subst i
      simp [b, hi, w']
    · rw [ite_eq_right hi]
      by_contra hne
      have hadj : (diagram M).Adj v i :=
        ⟨i.property.symm, hne, mt (hM.zero_comm _ _).mpr hne⟩
      have heq : i = w' := Subtype.ext (hu _ hadj)
      exact hi (congrArg e heq)
  have hcol (i : {j : ι // j ≠ v}) : M i v = if e i = k then a else 0 := by
    by_cases hi : e i = k
    · have heq : i = w' := e.injective hi
      subst i
      simp [a, hi, w']
    · rw [ite_eq_right hi]
      exact (hM.zero_comm _ _).mpr (by simpa [hi] using hrow i)
  have hfull : M.submatrix f f = leafExtension N k a b := by
    ext i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [Matrix.submatrix_apply, flast, fold, hM.diag, hrow, hcol, he]
  have hfinite : (leafExtension N k a b).IsFiniteCartan := by
    rw [← hfull]
    exact finiteCartan_submatrix hM f.injective
  have ha : a < 0 := ((diagram_adj_iff hM w v).mp hw.symm).2
  have htype := hclass k a b hfinite ha
  apply (hasIrreducibleCartanType_congr f.symm ?_).mpr htype
  intro i j
  have ht := congr_fun (congr_fun hfull (f.symm i)) (f.symm j)
  simpa using ht

theorem classification_from_leaf
    (hM : M.IsFiniteCartan) (v : ι) (hv : (diagram M).degree v = 1)
    (hsmall : HasIrreducibleCartanType
      (M.submatrix (Subtype.val : {i : ι // i ≠ v} → ι) Subtype.val)) :
    HasIrreducibleCartanType M := by
  rcases hsmall with ⟨n, hn, e, he⟩ | ⟨n, hn, e, he⟩ | ⟨n, hn, e, he⟩ |
    ⟨n, hn, e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
  · exact classification_from_leaf_numbering hM v hv (CartanMatrix.A n) e he
      (fun _ _ _ => leafExtension_A_classification)
  · exact classification_from_leaf_numbering hM v hv (CartanMatrix.B n) e he
      (fun _ _ _ => leafExtension_B_classification hn)
  · exact classification_from_leaf_numbering hM v hv (CartanMatrix.C n) e he
      (fun _ _ _ => leafExtension_C_classification hn)
  · exact classification_from_leaf_numbering hM v hv (CartanMatrix.D n) e he
      (fun _ _ _ => leafExtension_D_classification hn)
  · apply classification_from_leaf_numbering hM v hv (CartanMatrix.E 6) e he
    intro k a b hE ha
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (leafExtension_E6_hasCartanMatrix hE ha))))))
  · apply classification_from_leaf_numbering hM v hv (CartanMatrix.E 7) e he
    intro k a b hE ha
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (leafExtension_E7_hasCartanMatrix hE ha)))))))
  · apply classification_from_leaf_numbering hM v hv (CartanMatrix.E 8) e he
    intro k a b hE ha
    exact (not_finiteCartan_leafExtension_E8 ha hE).elim
  · apply classification_from_leaf_numbering hM v hv CartanMatrix.F₄ e he
    intro k a b hE ha
    exact (not_finiteCartan_leafExtension_F4 ha hE).elim
  · apply classification_from_leaf_numbering hM v hv CartanMatrix.G₂ e he
    intro k a b hE ha
    exact (not_finiteCartan_leafExtension_G2 ha hE).elim

theorem classification_of_connected :
    ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (M : Matrix ι ι ℤ), M.IsFiniteCartan → (diagram M).Connected →
        HasIrreducibleCartanType M := by
  suffices ∀ n : ℕ, ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι],
      Fintype.card ι = n → ∀ M : Matrix ι ι ℤ,
        M.IsFiniteCartan → (diagram M).Connected → HasIrreducibleCartanType M by
    intro ι _ _ _ M hM hconn
    exact this _ ι rfl M hM hconn
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ι _ _ _ hn M hM hconn
    classical
    by_cases hcard : Fintype.card ι = 1
    · have : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hcard.le
      let e : ι ≃ Fin 1 := Fintype.equivFinOfCardEq hcard
      refine Or.inl ⟨1, by omega, e, fun i j => ?_⟩
      have heq : i = j := Subsingleton.elim _ _
      subst j
      simp [hM.diag, CartanMatrix.A]
    · have hcardpos : 0 < Fintype.card ι := Fintype.card_pos
      have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      have htree : (diagram M).IsTree := ⟨hconn, diagram_isAcyclic hM⟩
      obtain ⟨v, hv⟩ := htree.exists_vert_degree_one_of_nontrivial
      let κ := {i : ι // i ≠ v}
      let N : Matrix κ κ ℤ := M.submatrix Subtype.val Subtype.val
      have hN : N.IsFiniteCartan := finiteCartan_submatrix hM Subtype.val_injective
      have hdiag : diagram N = (diagram M).induce ({v}ᶜ : Set ι) := by
        ext i j
        change (i ≠ j ∧ M i j ≠ 0 ∧ M j i ≠ 0) ↔
          (i.val ≠ j.val ∧ M i j ≠ 0 ∧ M j i ≠ 0)
        constructor
        · rintro ⟨hne, h1, h2⟩
          exact ⟨fun h => hne (Subtype.ext h), h1, h2⟩
        · rintro ⟨hne, h1, h2⟩
          exact ⟨fun h => hne (congrArg Subtype.val h), h1, h2⟩
      have hconnN : (diagram N).Connected := by
        rw [hdiag]
        exact hconn.induce_compl_singleton_of_degree_eq_one hv
      have : Nonempty κ := hconnN.nonempty
      have hlt : Fintype.card κ < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := v) (by simp)
      have hsmall := ih (Fintype.card κ) hlt κ rfl N hN hconnN
      exact classification_from_leaf hM v hv hsmall

end Langlands.LinearAlgebra.FiniteCartanMatrix

namespace Langlands.LinearAlgebra

theorem finiteCartanClassification : FiniteCartanClassificationStatement.{u} := by
  intro ι _ _ _ M hM hI
  exact FiniteCartanMatrix.classification_of_connected ι M hM
    (FiniteCartanMatrix.diagram_connected hM hI)

end Langlands.LinearAlgebra
