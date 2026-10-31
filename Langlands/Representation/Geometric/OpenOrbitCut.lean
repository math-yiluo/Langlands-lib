import Langlands.Representation.Geometric.ClosedSubgroupDefinitions
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section
namespace Langlands.Geometric.OrderedDoubleCosets
universe uG
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {P Q : Subgroup G} {n : ℕ}

/-- The stable partition of a finite index set into the indices satisfying a
predicate followed by the indices not satisfying it. -/
def openCutIndexEquiv (p : Fin n → Prop) [DecidablePred p] :
    Fin (Fintype.card {i : Fin n // p i} + Fintype.card {i : Fin n // ¬p i}) ≃ Fin n :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr
      (Fintype.orderIsoFinOfCardEq {i : Fin n // p i} rfl).toEquiv
      (Fintype.orderIsoFinOfCardEq {i : Fin n // ¬p i} rfl).toEquiv).trans
      (Equiv.sumCompl p))

omit [IsTopologicalGroup G] in
/-- Stable partition of an ordered orbit cover at an open union of its orbits. -/
theorem exists_openCut (s : OrderedDoubleCosets P Q n)
    (U : Set (Induction.LeftQuotient P)) (hU : IsOpen U)
    (p : Fin n → Prop)
    (hp : ∀ (i : Fin n) (x : Induction.LeftQuotient P),
      x ∈ cosetOrbit P Q (s.representative i) → (x ∈ U ↔ p i)) :
    ∃ (a b : ℕ) (e : Fin (a + b) ≃ Fin n)
      (t : OrderedDoubleCosets P Q (a + b)),
      (∀ i, t.representative i = s.representative (e i)) ∧
      t.initialOrbits ⟨a, by omega⟩ = U := by
  classical
  let a := Fintype.card {i : Fin n // p i}
  let b := Fintype.card {i : Fin n // ¬p i}
  let l : Fin a ≃o {i : Fin n // p i} := Fintype.orderIsoFinOfCardEq _ rfl
  let r : Fin b ≃o {i : Fin n // ¬p i} := Fintype.orderIsoFinOfCardEq _ rfl
  let e : Fin (a + b) ≃ Fin n := openCutIndexEquiv p
  have hel (i : Fin a) : e (i.castAdd b) = (l i).val := by
    change (Equiv.sumCompl p) ((Equiv.sumCongr l.toEquiv r.toEquiv)
      (finSumFinEquiv.symm (i.castAdd b))) = _
    rw [finSumFinEquiv_symm_apply_castAdd]
    rfl
  have her (i : Fin b) : e (i.natAdd a) = (r i).val := by
    change (Equiv.sumCompl p) ((Equiv.sumCongr l.toEquiv r.toEquiv)
      (finSumFinEquiv.symm (i.natAdd a))) = _
    rw [finSumFinEquiv_symm_apply_natAdd]
    rfl
  let O (k : Fin (a + b + 1)) : Set (Induction.LeftQuotient P) :=
    {x | ∃ i : Fin (a + b), i.val < k.val ∧ x ∈ cosetOrbit P Q (s.representative (e i))}
  have hcut : O ⟨a, by omega⟩ = U := by
    ext x
    constructor
    · rintro ⟨i, hi, hx⟩
      have hi' : i = (⟨i.val, hi⟩ : Fin a).castAdd b := Fin.ext rfl
      rw [hi', hel] at hx
      exact (hp _ _ hx).mpr (l _).property
    · intro hx
      obtain ⟨j, hj⟩ := s.covers x
      let i := l.symm ⟨j, (hp j x hj).mp hx⟩
      refine ⟨i.castAdd b, i.isLt, ?_⟩
      rw [hel]
      have heq : (l i).val = j := congrArg Subtype.val (l.apply_symm_apply _)
      rwa [heq]
  have hopen : ∀ k, IsOpen (O k) := by
    intro k
    by_cases hka : k.val < a
    · let j : Fin a := ⟨k.val, hka⟩
      have hset : O k = U ∩ s.initialOrbits (l j).val.castSucc := by
        ext x
        constructor
        · rintro ⟨i, hi, hx⟩
          have hia : i.val < a := lt_trans hi hka
          let z : Fin a := ⟨i.val, hia⟩
          have hiz : i = z.castAdd b := Fin.ext rfl
          rw [hiz, hel] at hx
          refine ⟨(hp _ _ hx).mpr (l z).property, (l z).val, ?_, hx⟩
          exact l.strictMono (show z < j from hi)
        · rintro ⟨hxU, i, hi, hx⟩
          let z := l.symm ⟨i, (hp i x hx).mp hxU⟩
          have hz : (l z).val = i := congrArg Subtype.val (l.apply_symm_apply _)
          refine ⟨z.castAdd b, ?_, ?_⟩
          · change z.val < j.val
            apply l.lt_iff_lt.mp
            change (l z).val < (l j).val
            rwa [hz]
          · rw [hel, hz]
            exact hx
      rw [hset]
      exact hU.inter (s.initial_open _)
    · by_cases hkb : k.val < a + b
      · let j : Fin b := ⟨k.val - a, by omega⟩
        have hset : O k = U ∪ s.initialOrbits (r j).val.castSucc := by
          ext x
          constructor
          · rintro ⟨i, hi, hx⟩
            by_cases hia : i.val < a
            · have hiz : i = (⟨i.val, hia⟩ : Fin a).castAdd b := Fin.ext rfl
              rw [hiz, hel] at hx
              exact Or.inl ((hp _ _ hx).mpr (l _).property)
            · let z : Fin b := ⟨i.val - a, by omega⟩
              have hiz : i = z.natAdd a := Fin.ext (by dsimp [z]; omega)
              rw [hiz, her] at hx
              refine Or.inr ⟨(r z).val, ?_, hx⟩
              exact r.strictMono (show z < j by change i.val - a < k.val - a; omega)
          · rintro (hx | ⟨i, hi, hx⟩)
            · have hm : (⟨a, by omega⟩ : Fin (a + b + 1)) ≤ k := by change a ≤ k.val; omega
              obtain ⟨z, hz, hx⟩ := hcut.symm ▸ hx
              exact ⟨z, lt_of_lt_of_le hz hm, hx⟩
            · by_cases hxU : x ∈ U
              · obtain ⟨z, hz, hx⟩ := hcut.symm ▸ hxU
                exact ⟨z, by change z.val < a at hz; omega, hx⟩
              · have hpi : ¬p i := fun h => hxU ((hp _ _ hx).mpr h)
                let z := r.symm ⟨i, hpi⟩
                have hz : (r z).val = i := congrArg Subtype.val (r.apply_symm_apply _)
                refine ⟨z.natAdd a, ?_, ?_⟩
                · have hlt : z < j := r.lt_iff_lt.mp (by change (r z).val < (r j).val; rwa [hz])
                  change a + z.val < k.val
                  change z.val < k.val - a at hlt
                  omega
                · rw [her, hz]
                  exact hx
        rw [hset]
        exact hU.union (s.initial_open _)
      · have hk : k.val = a + b := by omega
        have hset : O k = Set.univ := by
          apply Set.eq_univ_of_forall
          intro x
          obtain ⟨i, hi⟩ := s.covers x
          refine ⟨e.symm i, ?_, ?_⟩
          · rw [hk]; exact (e.symm i).isLt
          · simpa using hi
        rw [hset]
        exact isOpen_univ
  refine ⟨a, b, e, {
    representative := fun i => s.representative (e i)
    covers := ?_
    disjoint := ?_
    initial_open := hopen }, fun _ => rfl, hcut⟩
  · intro x
    obtain ⟨i, hi⟩ := s.covers x
    exact ⟨e.symm i, by simpa using hi⟩
  · intro i j hij
    exact s.disjoint (fun he => hij (e.injective he))

end Langlands.Geometric.OrderedDoubleCosets
