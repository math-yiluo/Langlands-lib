import Langlands.GroupScheme.SymplecticMatrix.Generation
import Mathlib.Data.Matrix.Basis

/-! # Symplectic matrices span the full matrix algebra -/

noncomputable section

namespace Langlands.GroupScheme.SymplecticInnerForm

open Matrix

variable {l : Type} [Fintype l] [DecidableEq l] {R : Type*} [CommRing R]

/-- Over any commutative ring, the standard symplectic matrices span the full
matrix algebra. No hypothesis on the cardinality or characteristic is needed. -/
theorem span_symplectic :
    Submodule.span R (Set.range (fun g : Matrix.symplecticGroup l R =>
      (g : Matrix (l ⊕ l) (l ⊕ l) R))) = ⊤ := by
  let P := Submodule.span R (Set.range (fun g : Matrix.symplecticGroup l R =>
    (g : Matrix (l ⊕ l) (l ⊕ l) R)))
  have hmem (g : Matrix.symplecticGroup l R) :
      (g : Matrix (l ⊕ l) (l ⊕ l) R) ∈ P :=
    Submodule.subset_span ⟨g, rfl⟩
  have hmul {X Y : Matrix (l ⊕ l) (l ⊕ l) R} (hX : X ∈ P) (hY : Y ∈ P) :
      X * Y ∈ P := by
    induction hX using Submodule.span_induction with
    | mem X hX =>
      obtain ⟨g, rfl⟩ := hX
      induction hY using Submodule.span_induction with
      | mem Y hY =>
        obtain ⟨h, rfl⟩ := hY
        exact hmem (g * h)
      | zero => simp
      | add Y Z _ _ hY hZ => simpa only [mul_add] using P.add_mem hY hZ
      | smul r Y _ hY => simpa only [mul_smul_comm] using P.smul_mem r hY
    | zero => simp
    | add X Z _ _ hX hZ => simpa only [add_mul] using P.add_mem hX hZ
    | smul r X _ hX => simpa only [smul_mul_assoc] using P.smul_mem r hX
  have h1 : (1 : Matrix (l ⊕ l) (l ⊕ l) R) ∈ P := hmem 1
  have hu (i : l) : single (Sum.inl i) (Sum.inr i) (1 : R) ∈ P := by
    have h := P.sub_mem
      (hmem ⟨SymplecticMatrix.upper (single i i 1),
        SymplecticMatrix.upper_mem (by simp [Matrix.IsSymm])⟩) h1
    have he : SymplecticMatrix.upper (single i i (1 : R)) - 1 =
        single (Sum.inl i) (Sum.inr i) 1 := by
      ext (a | a) (b | b) <;>
        simp [SymplecticMatrix.upper, Matrix.single, Matrix.one_apply]
    exact he ▸ h
  have hl (i : l) : single (Sum.inr i) (Sum.inl i) (1 : R) ∈ P := by
    have h := P.sub_mem
      (hmem ⟨SymplecticMatrix.lower (single i i 1),
        SymplecticMatrix.lower_mem (by simp [Matrix.IsSymm])⟩) h1
    have he : SymplecticMatrix.lower (single i i (1 : R)) - 1 =
        single (Sum.inr i) (Sum.inl i) 1 := by
      ext (a | a) (b | b) <;>
        simp [SymplecticMatrix.lower, Matrix.single, Matrix.one_apply]
    exact he ▸ h
  have hd₁ (i : l) : single (Sum.inl i) (Sum.inl i) (1 : R) ∈ P := by
    simpa using hmul (hu i) (hl i)
  have hd₂ (i : l) : single (Sum.inr i) (Sum.inr i) (1 : R) ∈ P := by
    simpa using hmul (hl i) (hu i)
  have hu' (i j : l) : single (Sum.inl i) (Sum.inr j) (1 : R) ∈ P := by
    by_cases hij : i = j
    · subst j
      exact hu i
    · let Y : Matrix l l R := single i j 1 + single j i 1
      have hY : Y.IsSymm := by simp [Y, Matrix.IsSymm, add_comm]
      have h := hmul (hmul (hd₁ i)
        (hmem ⟨SymplecticMatrix.upper Y, SymplecticMatrix.upper_mem hY⟩)) (hd₂ j)
      simpa [SymplecticMatrix.upper, Y, hij, Ne.symm hij] using h
  have hl' (i j : l) : single (Sum.inr i) (Sum.inl j) (1 : R) ∈ P := by
    by_cases hij : i = j
    · subst j
      exact hl i
    · let Y : Matrix l l R := single i j 1 + single j i 1
      have hY : Y.IsSymm := by simp [Y, Matrix.IsSymm, add_comm]
      have h := hmul (hmul (hd₂ i)
        (hmem ⟨SymplecticMatrix.lower Y, SymplecticMatrix.lower_mem hY⟩)) (hd₁ j)
      simpa [SymplecticMatrix.lower, Y, hij, Ne.symm hij] using h
  have hsingle₁ (i j : l ⊕ l) : single i j (1 : R) ∈ P := by
    rcases i with i | i <;> rcases j with j | j
    · simpa using hmul (hu' i j) (hl j)
    · exact hu' i j
    · exact hl' i j
    · simpa using hmul (hl' i j) (hu j)
  have hsingle (i j : l ⊕ l) (r : R) : single i j r ∈ P := by
    simpa only [smul_single, smul_eq_mul, mul_one] using P.smul_mem r (hsingle₁ i j)
  apply top_unique
  intro X _
  change X ∈ P
  rw [Matrix.matrix_eq_sum_single X]
  exact P.sum_mem fun i _ => P.sum_mem fun j _ => hsingle i j (X i j)

/-- Linear maps on the matrix algebra are determined by their values on
symplectic matrices, over every commutative coefficient ring. -/
theorem linearMap_ext_symplectic {V : Type*} [AddCommGroup V] [Module R V]
    (f g : Matrix (l ⊕ l) (l ⊕ l) R →ₗ[R] V)
    (h : ∀ x : Matrix.symplecticGroup l R, f x = g x) : f = g := by
  apply LinearMap.ext
  intro X
  have hx : X ∈ Submodule.span R (Set.range (fun x : Matrix.symplecticGroup l R =>
      (x : Matrix (l ⊕ l) (l ⊕ l) R))) := by
    rw [span_symplectic]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, rfl⟩ := hx
    exact h x
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smul, hx]

end Langlands.GroupScheme.SymplecticInnerForm
