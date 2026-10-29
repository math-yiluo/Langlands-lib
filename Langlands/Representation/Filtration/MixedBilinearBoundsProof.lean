import Langlands.Representation.Filtration.MixedBilinearBoundsStatement

/-! Mixed bilinear length bounds along actual finite filtrations. -/

noncomputable section

namespace Langlands.MixedBilinear

universe uK uG uH uI uV uW

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G] {H : Type uH} [Monoid H]
variable {I : Type uI}
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Each actual graded quotient in the first argument gives a bound for the next step. -/
theorem length_filtration_step_left {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (a : I → G) (b : I → H) (χ : I → k)
    (σ : Representation k H W) (j : Fin n) :
    length a b χ (s.subrepresentation j.succ).toRepresentation σ ≤
      length a b χ (s.subrepresentation j.castSucc).toRepresentation σ +
        length a b χ (s.gradedRepresentation j).ρ σ := by
  have hle : s.subrepresentation j.castSucc ≤ s.subrepresentation j.succ :=
    s.monotone_subrepresentation (Fin.castSucc_le_succ j)
  let S := (s.step j.castSucc).lowerInUpper (s.step j.succ)
    (CategoryTheory.Discrete.mk PUnit.unit)
  let e : S.toRepresentation.Equiv (s.subrepresentation j.castSucc).toRepresentation :=
    { toLinearMap :=
        { toFun := fun v => ⟨v.val.val, v.property⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl
      invFun := fun v => ⟨⟨v.val, hle v.property⟩, v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := length_le_restrict_add_quotient_left a b χ
    (s.subrepresentation j.succ).toRepresentation σ S
  exact h.trans (add_le_add (le_of_eq (length_congr_left b χ σ e)) le_rfl)

/-- A finite filtration of the first argument bounds the mixed form-space length by
its actual graded pieces. -/
theorem length_le_sum_left {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (a : I → G) (b : I → H) (χ : I → k)
    (σ : Representation k H W) :
    length a b χ A.ρ σ ≤ ∑ i : Fin n, length a b χ (s.gradedRepresentation i).ρ σ := by
  have key : ∀ j : ℕ, (hj : j ≤ n) →
      length a b χ (s.subrepresentation ⟨j, Nat.lt_succ_of_le hj⟩).toRepresentation σ ≤
        ∑ i : Fin j, length a b χ (s.gradedRepresentation
          ⟨i, lt_of_lt_of_le i.isLt hj⟩).ρ σ := by
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
      exact (length_filtration_step_left s a b χ σ ⟨j, hjn⟩).trans
        (add_le_add (ih hjn.le) le_rfl)
  have h := key n le_rfl
  have hl : (⟨n, Nat.lt_succ_of_le le_rfl⟩ : Fin (n + 1)) = Fin.last n := rfl
  rw [hl, s.subrepresentation_last, length_top_left] at h
  exact h

/-- The same bound in the second argument follows by swapping arguments and test maps. -/
theorem length_le_sum_right {B : Rep.{uW} k H} {n : ℕ}
    (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    (s : ObjectRepFiltration B n) :
    length a b χ ρ B.ρ ≤ ∑ j : Fin n, length a b χ ρ (s.gradedRepresentation j).ρ := by
  rw [length_flip]
  simpa only [length_flip a b χ ρ (s.gradedRepresentation _).ρ] using
    length_le_sum_left s b a χ ρ

/-- Filtrations of both arguments bound the mixed form-space length by the double sum
over all actual pairs of graded pieces. -/
theorem length_le_double_sum {A : Rep.{uV} k G} {B : Rep.{uW} k H} {m n : ℕ}
    (f : ObjectRepFiltration A m) (g : ObjectRepFiltration B n)
    (a : I → G) (b : I → H) (χ : I → k) :
    length a b χ A.ρ B.ρ ≤
      ∑ i : Fin m, ∑ j : Fin n,
        length a b χ (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ :=
  (length_le_sum_left f a b χ B.ρ).trans
    (Finset.sum_le_sum fun i _ => length_le_sum_right a b χ (f.gradedRepresentation i).ρ g)

/-- If every graded pair except a supplied one has length zero, the supplied pair
bounds the total mixed form-space length. -/
theorem length_le_of_single_pair {A : Rep.{uV} k G} {B : Rep.{uW} k H} {m n : ℕ}
    (f : ObjectRepFiltration A m) (g : ObjectRepFiltration B n)
    (a : I → G) (b : I → H) (χ : I → k) (i₀ : Fin m) (j₀ : Fin n)
    (hzero : ∀ i j, i ≠ i₀ ∨ j ≠ j₀ →
      length a b χ (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ = 0) :
    length a b χ A.ρ B.ρ ≤
      length a b χ (f.gradedRepresentation i₀).ρ (g.gradedRepresentation j₀).ρ := by
  classical
  have hsum : ∑ i : Fin m, ∑ j : Fin n,
        length a b χ (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ =
      length a b χ (f.gradedRepresentation i₀).ρ (g.gradedRepresentation j₀).ρ := by
    rw [Finset.sum_eq_single i₀]
    · exact Finset.sum_eq_single j₀ (fun j _ hj => hzero i₀ j (Or.inr hj))
        (fun h => (h (Finset.mem_univ j₀)).elim)
    · intro i _ hi
      exact Finset.sum_eq_zero (fun j _ => hzero i j (Or.inl hi))
    · intro h
      exact (h (Finset.mem_univ i₀)).elim
  exact hsum ▸ length_le_double_sum f g a b χ

/-- Mixed form-space length at most one makes every form a scalar multiple of any
nonzero form. -/
theorem exists_smul_eq_of_length_le_one (a : I → G) (b : I → H) (χ : I → k)
    (ρ : Representation k G V) (σ : Representation k H W)
    (h : length a b χ ρ σ ≤ 1) (B₀ B : forms a b χ ρ σ) (hB₀ : B₀ ≠ 0) :
    ∃ c : k, B = c • B₀ := by
  have hne : length a b χ ρ σ ≠ 0 := by
    intro hz
    have hs : Subsingleton (forms a b χ ρ σ) := Module.length_eq_zero_iff.mp hz
    exact hB₀ (hs.elim _ _)
  have hone : Module.length k (forms a b χ ρ σ) = 1 :=
    le_antisymm h (Order.one_le_iff_ne_zero.mpr hne)
  let : IsSimpleModule k (forms a b χ ρ σ) := Module.length_eq_one_iff.mp hone
  have hmem : B ∈ Submodule.span k {B₀} := by
    rw [IsSimpleModule.span_singleton_eq_top k hB₀]
    trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨c, hc.symm⟩

/-- Proof of `FiltrationLengthBoundStatement`. -/
theorem filtrationLengthBound :
    FiltrationLengthBoundStatement.{uK, uG, uH, uI, uV, uW} := by
  intro k _ G _ H _ I A B m n f g a b χ
  exact length_le_double_sum f g a b χ

/-- Proof of `SinglePairLengthBoundStatement`. -/
theorem singlePairLengthBound :
    SinglePairLengthBoundStatement.{uK, uG, uH, uI, uV, uW} := by
  intro k _ G _ H _ I A B m n f g a b χ i₀ j₀ hzero
  exact length_le_of_single_pair f g a b χ i₀ j₀ hzero

/-- Proof of `LengthOneProportionalityStatement`. -/
theorem lengthOneProportionality :
    LengthOneProportionalityStatement.{uK, uG, uH, uI, uV, uW} := by
  intro k _ G _ H _ I V W _ _ _ _ ρ σ a b χ h B₀ B hB₀
  exact exists_smul_eq_of_length_le_one a b χ ρ σ h B₀ B hB₀

/-- Proof of the aggregate `FiltrationBoundsStatement`. -/
theorem filtrationBounds : FiltrationBoundsStatement.{uK, uG, uH, uI, uV, uW} :=
  ⟨filtrationLengthBound, singlePairLengthBound, lengthOneProportionality⟩

end Langlands.MixedBilinear
