import Langlands.Representation.Intertwining.PQSupportOrbit
import Mathlib.Data.Fintype.Sort

/-! # Ordering a finite Bruhat lower set as the surviving support tail -/

noncomputable section

namespace Langlands.Geometric

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (P Q : Subgroup G)

/-- A finite enumeration reversing orbit closure has open prefixes. -/
def orderedDoubleCosetsOfAntitone {n : ℕ}
    (e : Fin n ≃ DoubleCoset.Quotient (P : Set G) Q)
    (he : ∀ x y, BruhatLE P Q x y → e.symm y ≤ e.symm x)
    (z : DoubleCoset.Quotient (P : Set G) Q → G)
    (hz : ∀ w, DoubleCoset.mk P Q (z w) = w) :
    OrderedDoubleCosets P Q n := by
  have : Finite (DoubleCoset.Quotient (P : Set G) Q) :=
    Finite.of_surjective e e.surjective
  refine {
    representative := fun i => (z (e i))⁻¹
    covers := ?_
    disjoint := ?_
    initial_open := ?_ }
  · intro x
    refine ⟨e.symm (leftQuotientDoubleCoset P Q x), ?_⟩
    rw [mem_cosetOrbit_inv_iff, hz, e.apply_symm_apply]
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    apply hij
    apply e.injective
    exact ((mem_cosetOrbit_inv_iff P Q _ x).mp hx |>.trans (hz _)).symm.trans
      ((mem_cosetOrbit_inv_iff P Q _ x).mp hy |>.trans (hz _))
  · intro k
    have hset :
        {x | ∃ i : Fin n, i.val < k.val ∧ x ∈ cosetOrbit P Q (z (e i))⁻¹} =
          (leftQuotientDoubleCoset P Q ⁻¹' {w | k.val ≤ (e.symm w).val})ᶜ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_preimage, not_le]
      constructor
      · rintro ⟨i, hi, hx⟩
        have hx' := (mem_cosetOrbit_inv_iff P Q _ x).mp hx
        rw [hz] at hx'
        simpa only [hx', e.symm_apply_apply] using hi
      · intro hx
        refine ⟨e.symm (leftQuotientDoubleCoset P Q x), hx, ?_⟩
        rw [mem_cosetOrbit_inv_iff, hz, e.apply_symm_apply]
    rw [hset]
    exact (isClosed_leftQuotientDoubleCoset_preimage P Q
      {w | k.val ≤ (e.symm w).val}
      (fun x y hxy hy => Nat.le_trans hy (he x y hxy))).isOpen_compl

@[simp]
theorem orderedDoubleCosetsOfAntitone_class {n : ℕ}
    (e : Fin n ≃ DoubleCoset.Quotient (P : Set G) Q)
    (he : ∀ x y, BruhatLE P Q x y → e.symm y ≤ e.symm x)
    (z : DoubleCoset.Quotient (P : Set G) Q → G)
    (hz : ∀ w, DoubleCoset.mk P Q (z w) = w) (i : Fin n) :
    (orderedDoubleCosetsOfAntitone P Q e he z hz).doubleCosetEquiv i = e i := by
  change DoubleCoset.mk P Q ((z (e i))⁻¹)⁻¹ = e i
  simpa only [inv_inv] using hz (e i)

/-- Every finite Bruhat lower set is exactly the last block of a finite open-prefix
orbit enumeration, with its own complete index equivalence. -/
theorem exists_lowerSet_tail_ordering
    [Finite (DoubleCoset.Quotient (P : Set G) Q)]
    (o : LinearOrder (DoubleCoset.Quotient (P : Set G) Q))
    (ho : IsBruhatRefinement P Q o)
    (T : Set (DoubleCoset.Quotient (P : Set G) Q))
    (hT : ∀ x y, BruhatLE P Q x y → y ∈ T → x ∈ T)
    (z : DoubleCoset.Quotient (P : Set G) Q → G)
    (hz : ∀ w, DoubleCoset.mk P Q (z w) = w) :
    ∃ a b, ∃ s : OrderedDoubleCosets P Q (a + b),
      ∃ c : Fin b ≃ T,
        s.initialOrbits ⟨a, by omega⟩ = (leftQuotientDoubleCoset P Q ⁻¹' T)ᶜ ∧
        ∀ i, s.doubleCosetEquiv (Fin.natAdd a i) = (c i).val := by
  classical
  let := Fintype.ofFinite (DoubleCoset.Quotient (P : Set G) Q)
  let := o
  let : LinearOrder (DoubleCoset.Quotient (P : Set G) Q) :=
    inferInstanceAs (LinearOrder (DoubleCoset.Quotient (P : Set G) Q)ᵒᵈ)
  let S : Finset (DoubleCoset.Quotient (P : Set G) Q) := Tᶜ.toFinset
  let a := S.card
  let b := Sᶜ.card
  let e : Fin (a + b) ≃ DoubleCoset.Quotient (P : Set G) Q :=
    finSumFinEquiv.symm.trans (finSumEquivOfFinset (s := S) rfl rfl)
  have hleft (i : Fin a) : e (Fin.castAdd b i) = S.orderEmbOfFin rfl i := by
    simp [e]
  have hright (i : Fin b) : e (Fin.natAdd a i) = Sᶜ.orderEmbOfFin rfl i := by
    simp [e]
  have hleftT (i : Fin a) : e (Fin.castAdd b i) ∉ T := by
    rw [hleft]
    simpa only [S, Set.mem_toFinset, Set.mem_compl_iff] using S.orderEmbOfFin_mem rfl i
  have hrightT (i : Fin b) : e (Fin.natAdd a i) ∈ T := by
    rw [hright]
    simpa only [Finset.mem_compl, S, Set.mem_toFinset, Set.mem_compl_iff, not_not]
      using Sᶜ.orderEmbOfFin_mem rfl i
  have he : ∀ x y, BruhatLE P Q x y → e.symm y ≤ e.symm x := by
    intro x y hxy
    obtain ⟨i, rfl⟩ := e.surjective x
    obtain ⟨j, rfl⟩ := e.surjective y
    simp only [e.symm_apply_apply]
    have horder : e j ≤ e i := ho _ _ hxy
    revert hxy horder
    refine Fin.addCases ?_ ?_ i <;> intro i
    · refine Fin.addCases ?_ ?_ j <;> intro j hxy horder
      · rw [hleft, hleft] at horder
        have hij := (S.orderEmbOfFin rfl).le_iff_le.mp horder
        exact hij
      · exact False.elim (hleftT i (hT _ _ hxy (hrightT j)))
    · refine Fin.addCases ?_ ?_ j <;> intro j hxy horder
      · change j.val ≤ a + i.val
        omega
      · rw [hright, hright] at horder
        have hij := (Sᶜ.orderEmbOfFin rfl).le_iff_le.mp horder
        simpa only [Fin.natAdd_le_natAdd_iff] using hij
  let s := orderedDoubleCosetsOfAntitone P Q e he z hz
  let c : Fin b ≃ T :=
    (Sᶜ.orderIsoOfFin rfl).toEquiv.trans
      (Set.equivOfEq (by ext w; simp [S]))
  refine ⟨a, b, s, c, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨i, hi, hxi⟩ hxT
      have hxi' : leftQuotientDoubleCoset P Q x = e i := by
        exact ((mem_cosetOrbit_inv_iff P Q _ x).mp hxi).trans (hz _)
      have hi' : i.val < a := hi
      have hieq : i = Fin.castAdd b ⟨i.val, hi'⟩ := Fin.ext rfl
      exact hleftT ⟨i.val, hi'⟩ (hieq ▸ hxi' ▸ hxT)
    · intro hxT
      let i := e.symm (leftQuotientDoubleCoset P Q x)
      have hi : i.val < a := by
        by_contra hi
        have hia : a ≤ i.val := Nat.le_of_not_gt hi
        let j : Fin b := ⟨i.val - a, by have := i.isLt; omega⟩
        have hij : i = Fin.natAdd a j := Fin.ext (by dsimp [j]; omega)
        apply hxT
        have h := hrightT j
        rw [← hij, e.apply_symm_apply] at h
        exact h
      refine ⟨i, hi, ?_⟩
      change x ∈ cosetOrbit P Q (z (e i))⁻¹
      rw [mem_cosetOrbit_inv_iff, hz, e.apply_symm_apply]
  · intro i
    rw [orderedDoubleCosetsOfAntitone_class, hright]
    rfl

end Langlands.Geometric
