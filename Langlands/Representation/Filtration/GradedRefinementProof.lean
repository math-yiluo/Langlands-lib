import Langlands.Representation.Filtration.GradedRefinementStatement
import Langlands.Representation.Filtration.IntervalLiftProof
import Mathlib.Logic.Equiv.Fin.Basic

namespace Langlands
namespace GradedRefinementProof

universe u v

/-- Split a dependent family over a successor finite index into its first and remaining fibers. -/
def sigmaFinSucc (n : ℕ) (β : Fin (n + 1) → Type u) :
    (β 0 ⊕ (Σ i : Fin n, β i.succ)) ≃ (Σ i : Fin (n + 1), β i) where
  toFun := Sum.elim (fun x => ⟨0, x⟩) (fun x => ⟨x.1.succ, x.2⟩)
  invFun x := Fin.cases (fun y => Sum.inl y) (fun i y => Sum.inr ⟨i, y⟩) x.1 x.2
  left_inv := by rintro (x | ⟨i, x⟩) <;> rfl
  right_inv := by
    rintro ⟨i, x⟩
    induction i using Fin.cases with
    | zero => rfl
    | succ i => rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Concatenation retains a bijection to all original steps and both endpoints of each step. -/
theorem concatenate {α : Type u} (r : SetRel α α) (n : ℕ)
    (p : Fin (n + 1) → α) (c : Fin n → RelSeries r)
    (hhead : ∀ i, (c i).head = p i.castSucc)
    (hlast : ∀ i, (c i).last = p i.succ) :
    ∃ d : RelSeries r, d.head = p 0 ∧ d.last = p (Fin.last n) ∧
      ∃ e : Fin d.length ≃ (Σ i, Fin (c i).length),
        ∀ j, d j.castSucc = c (e j).1 (e j).2.castSucc ∧
          d j.succ = c (e j).1 (e j).2.succ := by
  induction n with
  | zero =>
      refine ⟨RelSeries.singleton r (p 0), rfl, rfl, (show Fin 0 ≃ (Σ i : Fin 0, Fin (c i).length) from Equiv.equivOfIsEmpty _ _), ?_⟩
      intro j
      exact Fin.elim0 j
  | succ n ih =>
      obtain ⟨d, hd0, hd1, e, he⟩ := ih (fun i => p i.succ) (fun i => c i.succ)
        (fun i => hhead i.succ) (fun i => hlast i.succ)
      have hconnect : (c 0).last = d.head := (hlast 0).trans hd0.symm
      let result := (c 0).smash d hconnect
      let index : Fin ((c 0).length + d.length) ≃ (Σ i, Fin (c i).length) :=
        finSumFinEquiv.symm.trans ((Equiv.sumCongr (Equiv.refl _) e).trans
          (sigmaFinSucc n (fun i => Fin (c i).length)))
      have index_apply (x : Fin (c 0).length ⊕ Fin d.length) :
          index (finSumFinEquiv x) =
            sigmaFinSucc n (fun i => Fin (c i).length) ((Equiv.sumCongr (Equiv.refl _) e) x) :=
        congrArg (fun y => sigmaFinSucc n (fun i => Fin (c i).length)
          ((Equiv.sumCongr (Equiv.refl _) e) y)) (finSumFinEquiv.symm_apply_apply x)
      refine ⟨result, ?_, ?_, index, ?_⟩
      · exact (RelSeries.head_smash hconnect).trans (hhead 0)
      · exact (RelSeries.last_smash hconnect).trans hd1
      · change ∀ j : Fin ((c 0).length + d.length), _
        intro j
        obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective j
        rcases x with i | i
        · dsimp only [result, RelSeries.smash]
          rw [index_apply]
          change result (i.castAdd d.length).castSucc = c 0 i.castSucc ∧
            result (i.castAdd d.length).succ = c 0 i.succ
          exact ⟨RelSeries.smash_castAdd hconnect i, RelSeries.smash_succ_castAdd hconnect i⟩
        · dsimp only [result, RelSeries.smash]
          rw [index_apply]
          change result (i.natAdd (c 0).length).castSucc =
              c (e i).1.succ (e i).2.castSucc ∧
            result (i.natAdd (c 0).length).succ = c (e i).1.succ (e i).2.succ
          exact ⟨(RelSeries.smash_natAdd hconnect i).trans (he i).1,
            (RelSeries.smash_succ_natAdd hconnect i).trans (he i).2⟩

universe uK uG uA uB

open LengthCriterionProof

/-- Assemble interval chains in a permuted order of labels, preserving their actual factors. -/
theorem assemble {k : Type uK} [Field k] {G : Type uG} [Monoid G]
    {A : Rep.{uA} k G} {n : ℕ} (f : ObjectRepFiltration A n)
    (perm : Equiv.Perm (Fin n))
    (c : Fin n → RelSeries {(S, T) : Subrepresentation A.ρ × Subrepresentation A.ρ | S ⋖ T})
    (hhead : ∀ i, (c i).head = f.subrepresentation (perm i).castSucc)
    (hlast : ∀ i, (c i).last = f.subrepresentation (perm i).succ) :
    ∃ (m : ℕ) (s : ObjectRepFiltration A m), s.HasSimpleFactors ∧
      ∃ e : Fin m ≃ (Σ i, Fin (c i).length), ∀ j,
        Nonempty ((s.gradedRepresentation j).ρ.Equiv
          (quotientRep (c (e j).1 (e j).2.castSucc) (c (e j).1 (e j).2.succ))) := by
  obtain ⟨d, hd0, hd1, e, he⟩ := concatenate _ n f.subrepresentation
    (fun i => c (perm.symm i))
    (fun i => by simpa only [perm.apply_symm_apply] using hhead (perm.symm i))
    (fun i => by simpa only [perm.apply_symm_apply] using hlast (perm.symm i))
  let s : ObjectRepFiltration A d.length :=
    ObjectRepFiltration.ofSubrepresentations d
      (Fin.monotone_iff_le_succ.mpr (fun i => (d.step i).le))
      (hd0.trans f.subrepresentation_zero) (hd1.trans f.subrepresentation_last)
  refine ⟨d.length, s, ?_, e.trans (Equiv.sigmaCongrLeft (β := fun i => Fin (c i).length) perm.symm), ?_⟩
  · exact (hasSimpleFactors_iff_covBy s).mpr (fun i => d.step i)
  · intro j
    change Nonempty ((quotientRep (d j.castSucc) (d j.succ)).Equiv
      (quotientRep (c (perm.symm (e j).1) (e j).2.castSucc)
        (c (perm.symm (e j).1) (e j).2.succ)))
    rw [(he j).1, (he j).2]
    exact ⟨Representation.Equiv.refl _⟩

/-- Matching all steps of the lifted interval chains yields actual global factor matching. -/
theorem matching_of_chains {k : Type uK} [Field k] {G : Type uG} [Monoid G]
    {A : Rep.{uA} k G} {B : Rep.{uB} k G} {n : ℕ}
    (f : ObjectRepFiltration A n) (g : ObjectRepFiltration B n)
    (perm : Equiv.Perm (Fin n))
    (cA : Fin n → RelSeries {(S, T) : Subrepresentation A.ρ × Subrepresentation A.ρ | S ⋖ T})
    (cB : Fin n → RelSeries {(S, T) : Subrepresentation B.ρ × Subrepresentation B.ρ | S ⋖ T})
    (hA0 : ∀ i, (cA i).head = f.subrepresentation i.castSucc)
    (hA1 : ∀ i, (cA i).last = f.subrepresentation i.succ)
    (hB0 : ∀ i, (cB i).head = g.subrepresentation (perm i).castSucc)
    (hB1 : ∀ i, (cB i).last = g.subrepresentation (perm i).succ)
    (eqv : ∀ i, Fin (cA i).length ≃ Fin (cB i).length)
    (hmatch : ∀ i j, Nonempty ((quotientRep (cA i j.castSucc) (cA i j.succ)).Equiv
      (quotientRep (cB i (eqv i j).castSucc) (cB i (eqv i j).succ)))) :
    HaveSameJordanHolderFactors A B := by
  obtain ⟨a, s, hs, eA, hA⟩ := assemble f (Equiv.refl _) cA hA0 hA1
  obtain ⟨b, t, ht, eB, hB⟩ := assemble g perm cB hB0 hB1
  let E : Fin a ≃ Fin b := eA.trans ((Equiv.sigmaCongrRight eqv).trans eB.symm)
  have hab : a = b := Fin.equiv_iff_eq.mp ⟨E⟩
  subst b
  refine ⟨a, s, t, hs, ht, E, ?_⟩
  intro j
  obtain ⟨u⟩ := hA j
  obtain ⟨v⟩ := hmatch (eA j).1 (eA j).2
  obtain ⟨w⟩ := hB (E j)
  have hidx : eB (E j) = ⟨(eA j).1, eqv (eA j).1 (eA j).2⟩ :=
    eB.apply_symm_apply _
  rw [hidx] at w
  exact ⟨(u.trans v).trans w.symm⟩

/-- Assembly of the exact target from the two universe instances of quotient lifting. -/
private theorem refinement_of_lifting
    (liftA : ActualQuotientSeriesLiftStatement.{uK, uG, uA})
    (liftB : ActualQuotientSeriesLiftStatement.{uK, uG, uB}) :
    GradedJordanHolderRefinementStatement.{uK, uG, uA, uB} := by
  classical
  intro k _ G _ A B n f g perm H
  choose m s t hs ht e hmatch using H
  have LA (i : Fin n) := liftA k G A
    (f.subrepresentation i.castSucc) (f.subrepresentation i.succ)
    (f.monotone_subrepresentation (show i.castSucc < i.succ from Fin.castSucc_lt_succ).le) (m i) (s i) (hs i)
  have LB (i : Fin n) := liftB k G B
    (g.subrepresentation (perm i).castSucc) (g.subrepresentation (perm i).succ)
    (g.monotone_subrepresentation (show (perm i).castSucc < (perm i).succ from Fin.castSucc_lt_succ).le) (m i) (t i) (ht i)
  choose cA hA0 hA1 a ha using LA
  choose cB hB0 hB1 b hb using LB
  let eqv (i : Fin n) : Fin (cA i).length ≃ Fin (cB i).length :=
    (a i).trans ((e i).trans (b i).symm)
  apply matching_of_chains f g perm cA cB hA0 hA1 hB0 hB1 eqv
  intro i j
  obtain ⟨u⟩ := ha i j
  obtain ⟨v⟩ := hmatch i (a i j)
  obtain ⟨w⟩ := hb i (eqv i j)
  have hidx : b i (eqv i j) = e i (a i j) := (b i).apply_symm_apply _
  rw [hidx] at w
  exact ⟨(u.trans v).trans w.symm⟩

end GradedRefinementProof

universe uK uG uA uB

/-- Matching the actual Jordan–Hölder factors of every pair of graded pieces
matches the factors of the ambient representations. -/
theorem gradedJordanHolderRefinement :
    GradedJordanHolderRefinementStatement.{uK, uG, uA, uB} :=
  GradedRefinementProof.refinement_of_lifting
    actualQuotientSeriesLift.{uK, uG, uA}
    actualQuotientSeriesLift.{uK, uG, uB}

end Langlands
