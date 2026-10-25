import Langlands.Representation.Classification.OrderedExponentGroupingStatement
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Mathlib.Data.Fintype.Sort

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open GeneralLinear

private theorem weightedGrouping {n m : ℕ} (B : BlockShape n)
    (q : Fin B.length → Fin m) (hm : Monotone q) (hq : Function.Surjective q) :
    ∃ (D : BlockShape n) (hd : D.length = m)
      (S : ∀ j : Fin m, BlockShape (D.size (Fin.cast hd.symm j)))
      (e : ∀ j, Fin (S j).length ≃ {i : Fin B.length // q i = j})
      (h : ∀ j k, (S j).size k = B.size (e j k).val),
      (∀ j, StrictMono (fun k => (e j k).val)) ∧
      (∀ j k (x : Fin ((S j).size k)),
        D.index (Fin.cast hd.symm j) ((S j).index k x) =
          B.index (e j k).val (Fin.cast (h j k) x)) := by
  classical
  let Fiber (j : Fin m) := {i : Fin B.length // q i = j}
  let E (j : Fin m) : Fin (Fintype.card (Fiber j)) ≃o Fiber j :=
    Fintype.orderIsoFinOfCardEq (Fiber j) rfl
  let D : BlockShape n := {
    length := m
    size := fun j => ∑ i : Fiber j, B.size i.val
    positive := fun j => by
      obtain ⟨i, hi⟩ := hq j
      let : Nonempty (Fiber j) := ⟨⟨i, hi⟩⟩
      exact Finset.sum_pos (fun i _ => B.positive i.val) Finset.univ_nonempty
    sum_eq := by
      calc (∑ j, ∑ i : Fiber j, B.size i.val)
          = ∑ z : (j : Fin m) × Fiber j, B.size z.2.val :=
            (Fintype.sum_sigma' _).symm
        _ = ∑ i, B.size i :=
          Fintype.sum_equiv (Equiv.sigmaFiberEquiv q) _ _ (fun _ => rfl)
        _ = n := B.sum_eq }
  let S (j : Fin m) : BlockShape (D.size j) := {
    length := Fintype.card (Fiber j)
    size := fun k => B.size (E j k).val
    positive := fun k => B.positive _
    sum_eq := (E j).toEquiv.sum_comp (fun i => B.size i.val) }
  let φ : D.Index → Fin n := fun z =>
    B.index (E z.1 ((S z.1).indexEquiv.symm z.2).1).val
      ((S z.1).indexEquiv.symm z.2).2
  have hφ : ∀ x y, D.indexEquiv x < D.indexEquiv y → φ x < φ y := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    obtain ⟨⟨k, u⟩, rfl⟩ := (S i).indexEquiv.surjective x
    obtain ⟨⟨l, v⟩, rfl⟩ := (S j).indexEquiv.surjective y
    change D.index i ((S i).index k u) < D.index j ((S j).index l v) at hxy
    change B.index (E i ((S i).indexEquiv.symm ((S i).indexEquiv ⟨k, u⟩)).1).val
      ((S i).indexEquiv.symm ((S i).indexEquiv ⟨k, u⟩)).2 <
      B.index (E j ((S j).indexEquiv.symm ((S j).indexEquiv ⟨l, v⟩)).1).val
      ((S j).indexEquiv.symm ((S j).indexEquiv ⟨l, v⟩)).2
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases (D.index_lt_iff _ _).mp hxy with hij | ⟨rfl, hxy⟩
    · apply (B.index_lt_iff _ _).mpr
      apply Or.inl
      by_contra h
      have hle := hm (le_of_not_gt h)
      rw [(E j l).property, (E i k).property] at hle
      exact (not_le_of_gt hij) hle
    · have hinner : (S i).index k u < (S i).index l v := hxy
      rcases ((S i).index_lt_iff _ _).mp hinner with hkl | ⟨rfl, huv⟩
      · exact (B.index_lt_iff _ _).mpr (Or.inl ((E i).strictMono hkl))
      · exact (B.index_lt_iff _ _).mpr (Or.inr ⟨rfl, huv⟩)
  have hmono : StrictMono (φ ∘ D.indexEquiv.symm) := by
    intro x y hxy
    apply hφ
    simpa only [Equiv.apply_symm_apply] using hxy
  refine ⟨D, rfl, S, (fun j => (E j).toEquiv), (fun _ _ => rfl), ?_, ?_⟩
  · intro j k l hkl
    exact (E j).strictMono hkl
  · intro j k x
    have hfix : (φ ∘ D.indexEquiv.symm)
        (D.indexEquiv ⟨j, (S j).index k x⟩) =
        D.indexEquiv ⟨j, (S j).index k x⟩ :=
      le_antisymm hmono.apply_le hmono.le_apply
    have hfix' : φ ⟨j, (S j).index k x⟩ = D.index j ((S j).index k x) := by
      dsimp only [Function.comp_apply] at hfix
      rw [Equiv.symm_apply_apply] at hfix
      exact hfix
    change B.index (E j ((S j).indexEquiv.symm ((S j).indexEquiv ⟨k, x⟩)).1).val
      ((S j).indexEquiv.symm ((S j).indexEquiv ⟨k, x⟩)).2 = _ at hfix'
    rw [Equiv.symm_apply_apply] at hfix'
    exact hfix'.symm

/-- The finite weighted combinatorial step for consecutive exponent runs. -/
theorem orderedExponentGrouping : OrderedExponentGrouping := by
  classical
  intro n B a ha
  let r : Fin B.length → OrderDual ℝ := a
  generalize hcard : Fintype.card (Set.range r) = m
  let E := Fintype.orderIsoFinOfCardEq (Set.range r) hcard
  clear_value E
  clear hcard
  let q : Fin B.length → Fin m :=
    fun i => E.symm (Set.rangeFactorization r i)
  have hq : Function.Surjective q :=
    E.symm.surjective.comp Set.rangeFactorization_surjective
  have hm : Monotone q := by
    intro i j hij
    exact E.symm.monotone (ha hij)
  obtain ⟨D, hd, S, e, h, he, hc⟩ := weightedGrouping B q hm hq
  subst m
  refine ⟨D, (fun j => (E j).val), q, ?_, hm, hq, ?_, S, e, h, he, hc⟩
  · intro i j hij
    exact E.strictMono hij
  · intro i
    exact congrArg Subtype.val (E.apply_symm_apply (Set.rangeFactorization r i)) |>.symm

end Langlands.Classification
