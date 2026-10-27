import Langlands.Cohomology.Lie.CoefficientFunctoriality

/-! # Horizontal stability of the actual coefficient differential -/

noncomputable section

namespace Langlands.Cohomology.Lie

open scoped BigOperators

universe u v w ug

variable {K : Type u} [Field K] [CharZero K]
variable {L : Type v} [LieRing L] [LieAlgebra K L]
variable {M : Type w} [AddCommGroup M] [Module K M]
variable [LieRingModule L M] [LieModule K L M]

omit [LieRing L] in
private theorem omitNth_succ_cons {n : ℕ} (i : Fin (n + 1))
    (y : L) (x : Fin (n + 1) → L) :
    omitNth i.succ (Matrix.vecCons y x) =
      Matrix.vecCons y (omitNth i x) := by
  exact Fin.cons_comp_succ_succAbove y x i

omit [CharZero K] in
private theorem actionPart_cons_horizontal {n : ℕ} (H : Submodule K L)
    (f : Cochains K L M (n + 1))
    (hf : f ∈ Langlands.HorizontalAlternating.horizontal H (n + 1))
    (y : L) (hy : y ∈ H) (x : Fin (n + 1) → L) :
    actionPart (n + 1) f (Matrix.vecCons y x) = ⁅y, f x⁆ := by
  rw [actionPart_apply, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero, omitNth_zero]
  have hz : ∑ i : Fin (n + 1),
      (-1 : ℤ) ^ (i.succ : ℕ) •
        ⁅(Matrix.vecCons y x) i.succ, f (omitNth i.succ (Matrix.vecCons y x))⁆ = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [omitNth_succ_cons, hf (Matrix.vecCons y (omitNth i x)) 0 hy]
    simp
  rw [hz, add_zero]

omit [CharZero K] [LieRingModule L M] [LieModule K L M] in
private theorem signed_bracket_insertion {n : ℕ} (f : Cochains K L M (n + 1))
    (j : Fin (n + 1)) (a : L) (x : Fin (n + 1) → L) :
    (-1 : ℤ) ^ ((j : ℕ) + 1) • f (Matrix.vecCons a (omitNth j x)) =
      -f (Function.update x j a) := by
  have h := f.map_insertNth j a (omitNth j x)
  change f (j.insertNth a (j.removeNth x)) = _ at h
  rw [Fin.insertNth_removeNth] at h
  rw [h, pow_succ, mul_neg_one, neg_smul]

omit [LieRingModule L M] [LieModule K L M] in
private theorem bracketPart_cons_horizontal {n : ℕ} (H : Submodule K L)
    (f : Cochains K L M (n + 1))
    (hf : f ∈ Langlands.HorizontalAlternating.horizontal H (n + 1))
    (y : L) (hy : y ∈ H) (x : Fin (n + 1) → L) :
    bracketPart (n + 1) f (Matrix.vecCons y x) =
      -(∑ i, f (Function.update x i ⁅y, x i⁆)) := by
  rw [bracketPart_apply, Fin.sum_univ_succ]
  have hfirst :
      (∑ j ∈ Finset.Ici (0 : Fin (n + 1)),
        (-1 : ℤ) ^ (((0 : Fin (n + 1)) : ℕ) + (j : ℕ) + 1) •
          f (bracketFirst 0 j (Matrix.vecCons y x))) =
        -(∑ j, f (Function.update x j ⁅y, x j⁆)) := by
    rw [show Finset.Ici (0 : Fin (n + 1)) = Finset.univ by
      ext j
      simp]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.val_zero, zero_add, bracketFirst, Fin.castSucc_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, omitNth_zero]
    exact signed_bracket_insertion f j ⁅y, x j⁆ x
  rw [hfirst]
  suffices (∑ i : Fin n, ∑ j ∈ Finset.Ici i.succ,
      (-1 : ℤ) ^ ((i.succ : ℕ) + (j : ℕ) + 1) •
        f (bracketFirst i.succ j (Matrix.vecCons y x))) = 0 by
    rw [this, add_zero]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  have hij : i.succ ≤ j := Finset.mem_Ici.mp hj
  cases n with
  | zero => exact Fin.elim0 i
  | succ k =>
    cases j using Fin.cases with
    | zero => exact (not_le_of_gt (Fin.succ_pos i) hij).elim
    | succ j =>
      have hz : f (bracketFirst i.succ j.succ (Matrix.vecCons y x)) = 0 := by
        apply hf _ (1 : Fin (k + 2))
        simpa only [bracketFirst, ← Fin.succ_castSucc, omitNth_succ_cons,
          Matrix.cons_val_one, Matrix.cons_val_zero] using hy
      rw [hz, smul_zero]

/-- For a horizontal cochain, inserting a horizontal direction into its
coboundary is the coefficient action minus the bracket insertion sum. -/
theorem differential_cons_of_horizontal (H : Submodule K L) (q : ℕ)
    (f : Cochains K L M q)
    (hf : f ∈ Langlands.HorizontalAlternating.horizontal H q)
    (y : L) (hy : y ∈ H) (x : Fin q → L) :
    differential q f (Matrix.vecCons y x) =
      ⁅y, f x⁆ - ∑ i, f (Function.update x i ⁅y, x i⁆) := by
  cases q with
  | zero =>
    rw [differential_apply_zero]
    simp only [Matrix.cons_val_zero, Fin.sum_univ_zero, sub_zero]
    exact congrArg (fun z : Fin 0 → L => ⁅y, f z⁆) (Subsingleton.elim _ _)
  | succ n =>
    change actionPart (n + 1) f (Matrix.vecCons y x) +
      bracketPart (n + 1) f (Matrix.vecCons y x) = _
    rw [actionPart_cons_horizontal H f hf y hy x,
      bracketPart_cons_horizontal H f hf y hy x, sub_eq_add_neg]

/-- The actual coefficient differential preserves horizontality whenever
the cochain satisfies the infinitesimal insertion identity on `H`. -/
theorem differential_mem_horizontal (H : Submodule K L) (q : ℕ)
    (f : Cochains K L M q)
    (hf : f ∈ Langlands.HorizontalAlternating.horizontal H q)
    (hι : ∀ y ∈ H, ∀ x : Fin q → L,
      ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆)) :
    differential q f ∈ Langlands.HorizontalAlternating.horizontal H (q + 1) := by
  intro x i hi
  have hz : differential q f (Matrix.vecCons (x i) (i.removeNth x)) = 0 := by
    rw [differential_cons_of_horizontal H q f hf (x i) hi, hι (x i) hi, sub_self]
  have h := (differential q f).map_insertNth i (x i) (i.removeNth x)
  rw [Fin.insertNth_self_removeNth, hz, smul_zero] at h
  exact h

section FullGroup

variable {G : Type ug} [Group G]

/-- Restrict the actual differential to horizontal full-group-equivariant
cochains, using an explicitly supplied infinitesimal consequence of equivariance. -/
def horizontalEquivariantDifferential
    (H : Submodule K L) (σ : Representation K G L) (ρ : Representation K G M)
    (hσ : ∀ g x y, σ g ⁅x, y⁆ = ⁅σ g x, σ g y⁆)
    (hρ : ∀ g x m, ρ g ⁅x, m⁆ = ⁅σ g x, ρ g m⁆)
    (q : ℕ)
    (hι : ∀ f ∈ Langlands.HorizontalAlternating.submodule H σ ρ q,
      ∀ y ∈ H, ∀ x : Fin q → L,
        ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆)) :
    Langlands.HorizontalAlternating.submodule H σ ρ q →ₗ[K]
      Langlands.HorizontalAlternating.submodule H σ ρ (q + 1) where
  toFun f := ⟨differential q f.val,
    differential_mem_horizontal H q f.val f.property.1 (hι f.val f.property),
    differential_mem_equivariant σ ρ hσ hρ q f.val f.property.2⟩
  map_add' f h := Subtype.ext ((differential q).map_add f.val h.val)
  map_smul' a f := Subtype.ext ((differential q).map_smul a f.val)

@[simp]
theorem horizontalEquivariantDifferential_val
    (H : Submodule K L) (σ : Representation K G L) (ρ : Representation K G M)
    (hσ : ∀ g x y, σ g ⁅x, y⁆ = ⁅σ g x, σ g y⁆)
    (hρ : ∀ g x m, ρ g ⁅x, m⁆ = ⁅σ g x, ρ g m⁆)
    (q : ℕ)
    (hι : ∀ f ∈ Langlands.HorizontalAlternating.submodule H σ ρ q,
      ∀ y ∈ H, ∀ x : Fin q → L,
        ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆))
    (f : Langlands.HorizontalAlternating.submodule H σ ρ q) :
    (horizontalEquivariantDifferential H σ ρ hσ hρ q hι f).val =
      differential q f.val := rfl

end FullGroup

end Langlands.Cohomology.Lie
