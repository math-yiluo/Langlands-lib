import Langlands.Representation.Aubert.SignedCutComplex

/-! Contraction of cut diagrams along an invertible coordinate. -/

noncomputable section

namespace Langlands.Aubert.CutComplex

open scoped BigOperators

universe uI uM

variable {ι : Type uI} [LinearOrder ι]

@[simp] theorem sign_insert_self (s : Finset ι) (j : ι) :
    sign (insert j s) j = sign s j := by
  simp [sign, position, Finset.filter_insert]

@[simp] theorem sign_square (s : Finset ι) (j : ι) :
    sign s j * sign s j = 1 := by
  simp [sign, ← mul_pow]

theorem sign_mixed {s : Finset ι} {i j : ι}
    (hi : i ∈ s) (hj : j ∉ s) (hij : i ≠ j) :
    sign s i * sign (s.erase i) j =
      -(sign s j * sign (insert j s) i) := by
  rcases lt_or_gt_of_ne hij with h | h
  · have hcount := position_erase_of_lt hi h
    have hins : position (insert j s) i = position s i := by
      simp [position, Finset.filter_insert, not_lt_of_ge h.le]
    simp only [sign, hins]
    rw [← hcount, pow_succ]
    ring
  · have hcount : position (insert j s) i = position s i + 1 := by
      simp only [position, Finset.filter_insert, h, ↓reduceIte]
      exact Finset.card_insert_of_notMem (fun hmem => hj (Finset.mem_filter.mp hmem).1)
    have herase := position_erase_of_not_lt s (not_lt_of_ge h.le)
    simp only [sign, hcount, herase, pow_succ]
    ring

namespace Diagram

variable (D : Diagram.{uI,uM} ι) (j : ι)

/-- The insertion maps along one coordinate are linear equivalences. -/
structure InvertibleCoordinate where
  equiv : ∀ s, D.Obj s ≃ₗ[ℂ] D.Obj (insert j s)
  forward : ∀ s, (equiv s).toLinearMap = D.map (Finset.subset_insert j s)

namespace InvertibleCoordinate

variable {D j} (E : D.InvertibleCoordinate j)

theorem equiv_apply (s : Finset ι) (v : D.Obj s) :
    E.equiv s v = D.map (Finset.subset_insert j s) v :=
  LinearMap.congr_fun (E.forward s) v

theorem forward_inverse_total {s t : Finset ι} (hst : s ⊆ t)
    (ht : insert j s = t) (x : D.Total) :
    D.map hst ((E.equiv s).symm (x (insert j s))) = x t := by
  subst t
  rw [← E.equiv_apply, LinearEquiv.apply_symm_apply]

theorem inverse_natural {s t : Finset ι} (hst : s ⊆ t)
    (v : D.Obj (insert j s)) :
    D.map hst ((E.equiv s).symm v) =
      (E.equiv t).symm (D.map (Finset.insert_subset_insert j hst) v) := by
  apply (E.equiv t).injective
  rw [E.equiv_apply, D.map_map, LinearEquiv.apply_symm_apply]
  conv_rhs => rw [← (E.equiv s).apply_symm_apply v, E.equiv_apply]
  rw [D.map_map]

/-- Delete the chosen coordinate, using the inverse insertion map. -/
def homotopy : D.Total →ₗ[ℂ] D.Total where
  toFun x s := if j ∈ s then 0 else sign s j • (E.equiv s).symm (x (insert j s))
  map_add' x y := by
    funext s
    by_cases h : j ∈ s <;> simp [h, map_add, smul_add]
  map_smul' a x := by
    funext s
    by_cases h : j ∈ s
    · simp [h]
    · simp only [h, ↓reduceIte, Pi.smul_apply, map_smul, RingHom.id_apply]
      exact smul_comm _ _ _

@[simp] theorem homotopy_apply (x : D.Total) (s : Finset ι) :
    E.homotopy x s =
      if j ∈ s then 0 else sign s j • (E.equiv s).symm (x (insert j s)) := rfl

theorem diagonal (x : D.Total) :
    D.step j (E.homotopy x) + E.homotopy (D.step j x) = x := by
  funext s
  by_cases hj : j ∈ s
  · simp only [Pi.add_apply, step_apply, hj, ↓reduceIte, homotopy_apply,
      Finset.notMem_erase, map_smul, add_zero]
    have hs : insert j (s.erase j) = s := Finset.insert_erase hj
    have hc : D.map (Finset.erase_subset j s)
        ((E.equiv (s.erase j)).symm (x (insert j (s.erase j)))) = x s := by
      exact E.forward_inverse_total _ hs x
    rw [hc]
    have hsign : sign (s.erase j) j = sign s j := by
      rw [← sign_insert_self (s.erase j) j, hs]
    rw [hsign, smul_smul, sign_square, one_smul]
  · simp only [Pi.add_apply, step_apply, hj, ↓reduceIte, homotopy_apply,
      Finset.mem_insert_self, map_smul, zero_add, sign_insert_self]
    rw [D.map_apply_congr (Finset.erase_insert hj) _ (Finset.subset_insert j s) x]
    rw [← E.equiv_apply, LinearEquiv.symm_apply_apply, smul_smul,
      sign_square, one_smul]

theorem off_diagonal (i : ι) (hij : i ≠ j) (x : D.Total) :
    D.step i (E.homotopy x) + E.homotopy (D.step i x) = 0 := by
  funext s
  have hji : j ≠ i := Ne.symm hij
  by_cases hj : j ∈ s
  · by_cases hi : i ∈ s <;> simp [hi, hj, hji]
  · by_cases hi : i ∈ s
    · have hj' : j ∉ s.erase i := fun hmem => hj (Finset.mem_of_mem_erase hmem)
      have hi' : i ∈ insert j s := Finset.mem_insert_of_mem hi
      simp only [Pi.add_apply, step_apply, hi, hj, hj', hi', homotopy_apply,
        ↓reduceIte, map_smul, smul_smul, Pi.zero_apply]
      have hmaps : D.map (Finset.erase_subset i s)
          ((E.equiv (s.erase i)).symm (x (insert j (s.erase i)))) =
          (E.equiv s).symm (D.map (Finset.erase_subset i (insert j s))
            (x ((insert j s).erase i))) := by
        rw [E.inverse_natural]
        congr 1
        exact D.map_apply_congr (Finset.erase_insert_of_ne hji).symm _ _ x
      rw [hmaps, sign_mixed hi hj hij, neg_smul, neg_add_cancel]
    · simp [hi, hj, hij]

variable [Fintype ι]

/-- The inverse insertion is a contracting homotopy for the signed differential. -/
theorem contraction (x : D.Total) :
    D.differential (E.homotopy x) + E.homotopy (D.differential x) = x := by
  simp only [differential_apply, map_sum]
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_eq_single j]
  · exact E.diagonal x
  · intro i _ hij
    exact E.off_diagonal i hij x
  · simp

include E in
/-- Every cocycle of the total cut complex is a boundary. -/
theorem exists_boundary (x : D.Total) (hx : D.differential x = 0) :
    ∃ y, D.differential y = x := by
  refine ⟨E.homotopy x, ?_⟩
  simpa [hx] using E.contraction x

omit [Fintype ι] in
theorem homotopy_vanishes_off_degree (k : ℕ) (x : D.Total)
    (hx : ∀ s, s.card ≠ k + 1 → x s = 0) (s : Finset ι) (hs : s.card ≠ k) :
    E.homotopy x s = 0 := by
  by_cases hj : j ∈ s
  · simp [hj]
  · have hcard : (insert j s).card ≠ k + 1 := by
      rw [Finset.card_insert_of_notMem hj]
      omega
    simp [hj, hx _ hcard]

/-- The homogeneous degree-lowering homotopy. -/
def degreeHomotopy (k : ℕ) : D.Degree (k + 1) →ₗ[ℂ] D.Degree k :=
  D.restrict k ∘ₗ E.homotopy ∘ₗ D.extend (k + 1)

omit [Fintype ι] in
theorem extend_degreeHomotopy (k : ℕ) (x : D.Degree (k + 1)) :
    D.extend k (E.degreeHomotopy k x) = E.homotopy (D.extend (k + 1) x) := by
  funext s
  by_cases hs : s.card = k
  · simp [hs, degreeHomotopy]
  · rw [extend_apply, dite_eq_right hs]
    symm
    apply E.homotopy_vanishes_off_degree k (D.extend (k + 1) x) _ s hs
    intro t ht
    simp [ht]

theorem degree_contraction (k : ℕ) (x : D.Degree (k + 1)) :
    D.degreeDifferential k (E.degreeHomotopy k x) +
      E.degreeHomotopy (k + 1) (D.degreeDifferential (k + 1) x) = x := by
  apply D.extend_injective (k + 1)
  rw [map_add, D.extend_degreeDifferential, E.extend_degreeHomotopy,
    E.extend_degreeHomotopy, D.extend_degreeDifferential]
  exact E.contraction _

include E in
theorem range_degreeDifferential_eq_ker (k : ℕ) :
    LinearMap.range (D.degreeDifferential k) =
      LinearMap.ker (D.degreeDifferential (k + 1)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact D.degreeDifferential_square k y
  · intro hx
    refine ⟨E.degreeHomotopy k x, ?_⟩
    simpa [LinearMap.mem_ker.mp hx] using E.degree_contraction k x

omit [Fintype ι] in
theorem homotopy_extend_zero (x : D.Degree 0) :
    E.homotopy (D.extend 0 x) = 0 := by
  funext s
  by_cases hj : j ∈ s
  · simp [hj]
  · simp [hj]

include E in
theorem degree_zero_cocycle_eq_zero (x : D.Degree 0)
    (hx : D.degreeDifferential 0 x = 0) : x = 0 := by
  apply D.extend_injective 0
  have hdx : D.differential (D.extend 0 x) = 0 := by
    rw [← D.extend_degreeDifferential, hx, map_zero]
  have hc := E.contraction (D.extend 0 x)
  simpa [hdx, E.homotopy_extend_zero x] using hc.symm

include E in
theorem degree_zero_injective : Function.Injective (D.degreeDifferential 0) := by
  intro x y hxy
  have hz : D.degreeDifferential 0 (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (E.degree_zero_cocycle_eq_zero _ hz)

end InvertibleCoordinate
end Diagram

namespace BooleanInterval

variable (lower upper : Finset ι)
variable (M : Type uM) [AddCommGroup M] [Module ℂ M]

/-- The interval of cut sets between the required and allowed sets. -/
def Active (s : Finset ι) : Prop := lower ⊆ s ∧ s ⊆ upper

/-- A constant coefficient module on the interval and the zero module elsewhere. -/
def diagram : Diagram.{uI,uM} ι := by
  classical
  exact {
  Obj s := PLift (Active lower upper s) → M
  add _ := inferInstance
  module _ := inferInstance
  map {s t} hst :=
    { toFun := fun x _ => if hs : Active lower upper s then x ⟨hs⟩ else 0
      map_add' := by
        intro x y
        funext ht
        by_cases hs : Active lower upper s <;> simp [hs]
      map_smul' := by
        intro a x
        funext ht
        by_cases hs : Active lower upper s <;> simp [hs] }
  map_refl := fun s => by
    apply LinearMap.ext
    intro x
    funext hs
    simp [hs.down]
  map_comp := fun {s t u} hst htu => by
    apply LinearMap.ext
    intro x
    funext hu
    by_cases hs : Active lower upper s
    · have ht : Active lower upper t := ⟨hs.1.trans hst, htu.trans hu.down.2⟩
      simp [hs, ht]
    · simp [hs] }

theorem active_insert_iff (j : ι) (hjUpper : j ∈ upper) (hjLower : j ∉ lower)
    (s : Finset ι) :
    Active lower upper (insert j s) ↔ Active lower upper s := by
  constructor
  · rintro ⟨hl, hu⟩
    refine ⟨?_, (Finset.subset_insert j s).trans hu⟩
    intro i hi
    rcases Finset.mem_insert.mp (hl hi) with h | h
    · exact False.elim (hjLower (h ▸ hi))
    · exact h
  · rintro ⟨hl, hu⟩
    exact ⟨hl.trans (Finset.subset_insert j s), Finset.insert_subset hjUpper hu⟩

/-- A free coordinate of the interval gives invertible insertion maps. -/
def invertibleCoordinate (j : ι) (hjUpper : j ∈ upper) (hjLower : j ∉ lower) :
    (diagram lower upper M).InvertibleCoordinate j where
  equiv s :=
    { toFun := fun x ht =>
        x ⟨(active_insert_iff lower upper j hjUpper hjLower s).mp ht.down⟩
      invFun := fun y hs =>
        y ⟨(active_insert_iff lower upper j hjUpper hjLower s).mpr hs.down⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  forward s := by
    apply LinearMap.ext
    intro x
    funext ht
    have hs := (active_insert_iff lower upper j hjUpper hjLower s).mp ht.down
    simp [diagram, hs]
    rfl

omit [LinearOrder ι] in
theorem active_singleton_iff (s : Finset ι) :
    Active lower lower s ↔ s = lower := by
  exact ⟨fun h => Finset.Subset.antisymm h.2 h.1, fun h => h ▸ ⟨by rfl, by rfl⟩⟩

theorem singleton_degree_subsingleton (k : ℕ) (hk : k ≠ lower.card) :
    Subsingleton ((diagram lower lower M).Degree k) := by
  constructor
  intro x y
  funext s hs
  have heq := (active_singleton_iff lower s.1).mp hs.down
  exact False.elim (hk (s.property.symm.trans (congrArg Finset.card heq)))

/-- A singleton interval retains exactly its coefficient module in its own degree. -/
def singletonDegreeEquiv :
    (diagram lower lower M).Degree lower.card ≃ₗ[ℂ] M where
  toFun x := x ⟨lower, rfl⟩ ⟨⟨Finset.Subset.rfl, Finset.Subset.rfl⟩⟩
  invFun y := fun _ _ => y
  left_inv x := by
    funext s hs
    have heq : s = ⟨lower, rfl⟩ :=
      Subtype.ext ((active_singleton_iff lower s.1).mp hs.down)
    subst s
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [Fintype ι]

theorem exact_of_free_coordinate (j : ι) (hjUpper : j ∈ upper) (hjLower : j ∉ lower)
    (k : ℕ) :
    LinearMap.range ((diagram lower upper M).degreeDifferential k) =
      LinearMap.ker ((diagram lower upper M).degreeDifferential (k + 1)) :=
  (invertibleCoordinate lower upper M j hjUpper hjLower).range_degreeDifferential_eq_ker k

theorem injective_start_of_free_coordinate
    (j : ι) (hjUpper : j ∈ upper) (hjLower : j ∉ lower) :
    Function.Injective ((diagram lower upper M).degreeDifferential 0) :=
  (invertibleCoordinate lower upper M j hjUpper hjLower).degree_zero_injective

theorem singleton_differential_zero (k : ℕ) :
    (diagram lower lower M).degreeDifferential k = 0 := by
  by_cases hk : k = lower.card
  · have := singleton_degree_subsingleton lower M (k + 1) (by omega)
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  · have := singleton_degree_subsingleton lower M k hk
    apply LinearMap.ext
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]

/-- Concentration below the largest allowed degree, retaining singleton homology. -/
theorem exact_below_allowed (hlu : lower ⊆ upper) (k : ℕ)
    (hk : k + 1 < upper.card) :
    LinearMap.range ((diagram lower upper M).degreeDifferential k) =
      LinearMap.ker ((diagram lower upper M).degreeDifferential (k + 1)) := by
  by_cases heq : lower = upper
  · subst upper
    have := singleton_degree_subsingleton lower M (k + 1) (by omega)
    exact Subsingleton.elim _ _
  · have hnot : ¬ upper ⊆ lower := fun h => heq (Finset.Subset.antisymm hlu h)
    obtain ⟨j, hju, hjl⟩ := Finset.not_subset.mp hnot
    exact exact_of_free_coordinate lower upper M j hju hjl k

theorem injective_before_allowed (hlu : lower ⊆ upper) (hcard : 0 < upper.card) :
    Function.Injective ((diagram lower upper M).degreeDifferential 0) := by
  by_cases heq : lower = upper
  · subst upper
    have := singleton_degree_subsingleton lower M 0 (by omega)
    intro x y _
    exact Subsingleton.elim _ _
  · have hnot : ¬ upper ⊆ lower := fun h => heq (Finset.Subset.antisymm hlu h)
    obtain ⟨j, hju, hjl⟩ := Finset.not_subset.mp hnot
    exact injective_start_of_free_coordinate lower upper M j hju hjl

end BooleanInterval
end Langlands.Aubert.CutComplex
