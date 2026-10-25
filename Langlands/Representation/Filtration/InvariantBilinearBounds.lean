import Langlands.Representation.Filtration.InvariantBilinear

/-! Covariant bilinear length bounds along actual finite filtrations. -/

noncomputable section

namespace Langlands.InvariantBilinear

universe uK uG uV uW

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Each actual graded quotient gives a bound for the next step. -/
theorem length_filtration_step_left {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (σ : Representation k G W) (χ : G → k)
    (j : Fin n) :
    length (s.subrepresentation j.succ).toRepresentation σ χ ≤
      length (s.subrepresentation j.castSucc).toRepresentation σ χ +
        length (s.gradedRepresentation j).ρ σ χ := by
  have hle : s.subrepresentation j.castSucc ≤ s.subrepresentation j.succ :=
    s.monotone_subrepresentation (Fin.castSucc_le_succ j)
  let S := (s.step j.castSucc).lowerInUpper (s.step j.succ) (CategoryTheory.Discrete.mk PUnit.unit)
  let e : S.toRepresentation.Equiv (s.subrepresentation j.castSucc).toRepresentation :=
    { toLinearMap :=
        { toFun := fun v => ⟨v.val.val, v.property⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl
      invFun := fun v => ⟨⟨v.val, hle v.property⟩, v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := length_le_subrepresentation_add_quotient
    (s.subrepresentation j.succ).toRepresentation σ χ S
  exact h.trans (add_le_add (le_of_eq (length_congr_left σ χ e)) le_rfl)

/-- A finite filtration bounds the bilinear-form space by its graded pieces. -/
theorem length_le_sum_left {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (σ : Representation k G W) (χ : G → k) :
    length A.ρ σ χ ≤ ∑ i : Fin n, length (s.gradedRepresentation i).ρ σ χ := by
  have key : ∀ j : ℕ, (hj : j ≤ n) →
      length (s.subrepresentation ⟨j, Nat.lt_succ_of_le hj⟩).toRepresentation σ χ ≤
        ∑ i : Fin j, length (s.gradedRepresentation
          ⟨i, lt_of_lt_of_le i.isLt hj⟩).ρ σ χ := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h0 : s.subrepresentation ⟨0, Nat.lt_succ_of_le hj⟩ = ⊥ :=
        s.subrepresentation_zero
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rw [h0, length_bot_left]
    | succ j ih =>
      intro hj
      have hjn : j < n := hj
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      exact (length_filtration_step_left s σ χ ⟨j, hjn⟩).trans
        (add_le_add (ih hjn.le) le_rfl)
  have h := key n le_rfl
  have hl : (⟨n, Nat.lt_succ_of_le le_rfl⟩ : Fin (n + 1)) = Fin.last n := rfl
  rw [hl, s.subrepresentation_last, length_top_left] at h
  exact h

/-- The same bound in the second argument follows by swapping arguments. -/
theorem length_le_sum_right {A : Rep.{uW} k G} {n : ℕ}
    (ρ : Representation k G V) (s : ObjectRepFiltration A n) (χ : G → k) :
    length ρ A.ρ χ ≤ ∑ i : Fin n, length ρ (s.gradedRepresentation i).ρ χ := by
  rw [length_flip]
  simpa only [length_flip (s.gradedRepresentation _).ρ ρ χ] using
    length_le_sum_left s ρ χ

/-- The sum of lengths on all actual pairs of graded factors, with multiplicity. -/
def gradedLengthSum {A : Rep.{uV} k G} {B : Rep.{uW} k G} {m n : ℕ}
    (s : ObjectRepFiltration A m) (t : ObjectRepFiltration B n) (χ : G → k) : ℕ∞ :=
  ∑ i : Fin m, ∑ j : Fin n,
    length (s.gradedRepresentation i).ρ (t.gradedRepresentation j).ρ χ

/-- Restriction in both arguments bounds length by the full double sum. -/
theorem length_le_gradedLengthSum {A : Rep.{uV} k G} {B : Rep.{uW} k G} {m n : ℕ}
    (s : ObjectRepFiltration A m) (t : ObjectRepFiltration B n) (χ : G → k) :
    length A.ρ B.ρ χ ≤ gradedLengthSum s t χ := by
  apply (length_le_sum_left s B.ρ χ).trans
  exact Finset.sum_le_sum (fun i _ => length_le_sum_right (s.gradedRepresentation i).ρ t χ)

/-- If only one pair of graded factors can contribute, its length bounds the total. -/
theorem length_le_of_single_pair {A : Rep.{uV} k G} {B : Rep.{uW} k G} {m n : ℕ}
    (s : ObjectRepFiltration A m) (t : ObjectRepFiltration B n) (χ : G → k)
    (i₀ : Fin m) (j₀ : Fin n)
    (hzero : ∀ i j, i ≠ i₀ ∨ j ≠ j₀ →
      length (s.gradedRepresentation i).ρ (t.gradedRepresentation j).ρ χ = 0) :
    length A.ρ B.ρ χ ≤ length (s.gradedRepresentation i₀).ρ (t.gradedRepresentation j₀).ρ χ := by
  classical
  have hsum : gradedLengthSum s t χ =
      length (s.gradedRepresentation i₀).ρ (t.gradedRepresentation j₀).ρ χ := by
    unfold gradedLengthSum
    rw [Finset.sum_eq_single i₀]
    · exact Finset.sum_eq_single j₀ (fun j _ hj => hzero i₀ j (Or.inr hj))
        (fun h => (h (Finset.mem_univ j₀)).elim)
    · intro i _ hi
      exact Finset.sum_eq_zero (fun j _ => hzero i j (Or.inl hi))
    · intro h
      exact (h (Finset.mem_univ i₀)).elim
  exact hsum ▸ length_le_gradedLengthSum s t χ

/-- A form-space length bound by one gives proportionality to every nonzero form. -/
theorem exists_smul_eq_of_length_le_one
    (ρ : Representation k G V) (σ : Representation k G W) (χ : G → k)
    (h : length ρ σ χ ≤ 1) (B C : forms ρ σ χ) (hB : B ≠ 0) :
    ∃ a : k, C = a • B := by
  have hne : length ρ σ χ ≠ 0 := by
    intro hz
    have hs : Subsingleton (forms ρ σ χ) := Module.length_eq_zero_iff.mp hz
    exact hB (hs.elim _ _)
  have hone : Module.length k (forms ρ σ χ) = 1 :=
    le_antisymm h (Order.one_le_iff_ne_zero.mpr hne)
  let : IsSimpleModule k (forms ρ σ χ) := Module.length_eq_one_iff.mp hone
  have hmem : C ∈ Submodule.span k {B} := by
    rw [IsSimpleModule.span_singleton_eq_top k hB]
    trivial
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨a, ha.symm⟩

/-- One potentially nonzero graded pair of length at most one gives proportionality. -/
theorem exists_smul_eq_of_single_pair
    {A : Rep.{uV} k G} {D : Rep.{uW} k G} {m n : ℕ}
    (s : ObjectRepFiltration A m) (t : ObjectRepFiltration D n) (χ : G → k)
    (i₀ : Fin m) (j₀ : Fin n)
    (hzero : ∀ i j, i ≠ i₀ ∨ j ≠ j₀ →
      length (s.gradedRepresentation i).ρ (t.gradedRepresentation j).ρ χ = 0)
    (hone : length (s.gradedRepresentation i₀).ρ (t.gradedRepresentation j₀).ρ χ ≤ 1)
    (B C : forms A.ρ D.ρ χ) (hB : B ≠ 0) : ∃ a : k, C = a • B :=
  exists_smul_eq_of_length_le_one A.ρ D.ρ χ
    ((length_le_of_single_pair s t χ i₀ j₀ hzero).trans hone) B C hB

end Langlands.InvariantBilinear
