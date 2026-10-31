import Langlands.Algebra.SymmetricAlgebraHomogeneous
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Degree.Support

/-! # Homogeneous components of symmetric tensor modules -/

noncomputable section
universe uR uM uV uN uW
set_option autoImplicit false
open scoped TensorProduct

namespace Langlands.Algebra.SymmetricGrading

variable (R : Type uR) (M : Type uM) (V : Type uV)
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V]

local notation "S" => SymmetricAlgebra R M
local notation "T" => S ⊗[R] V

/-- Degree projection on the symmetric factor of the actual tensor module. -/
def tensorComponent (d : ℕ) : T →ₗ[R] T :=
  TensorProduct.map (component R M d) (LinearMap.id : V →ₗ[R] V)

@[simp]
theorem tensorComponent_tmul (d : ℕ) (P : S) (v : V) :
    tensorComponent R M V d (P ⊗ₜ[R] v) = component R M d P ⊗ₜ[R] v := rfl

/-- Homogeneity means membership in the image of the canonical degree projection. -/
def IsHomogeneousTensor (d : ℕ) (x : T) : Prop :=
  tensorComponent R M V d x = x

theorem tensorComponent_component (d e : ℕ) (x : T) :
    tensorComponent R M V d (tensorComponent R M V e x) =
      if e = d then tensorComponent R M V e x else 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul P v =>
    simp only [tensorComponent_tmul, component_component]
    split_ifs <;> simp
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    split_ifs <;> simp

theorem tensorComponent_isHomogeneous (d : ℕ) (x : T) :
    IsHomogeneousTensor R M V d (tensorComponent R M V d x) := by
  simp only [IsHomogeneousTensor, tensorComponent_component, ↓reduceIte]

theorem tensorComponent_of_isHomogeneous (d : ℕ) {e : ℕ} {x : T}
    (hx : IsHomogeneousTensor R M V e x) :
    tensorComponent R M V d x = if e = d then x else 0 := by
  rw [← hx, tensorComponent_component]

/-- Multiplication in the symmetric coefficient ring gives degree convolution. -/
theorem tensorComponent_smul (d : ℕ) (P : S) (x : T) :
    tensorComponent R M V d (P • x) =
      ∑ a ∈ Finset.antidiagonal d,
        component R M a.1 P • tensorComponent R M V a.2 x := by
  induction x using TensorProduct.inductionOn with
  | tmul Q v =>
    simp only [TensorProduct.smul_tmul', smul_eq_mul, tensorComponent_tmul,
      component_mul, TensorProduct.sum_tmul]
  | add x y hx hy =>
    simp only [smul_add, map_add, hx, hy, Finset.sum_add_distrib]

/-- A homogeneous tensor selects the unique complementary coefficient degree. -/
theorem tensorComponent_smul_of_isHomogeneous (d : ℕ) (P : S) {e : ℕ} {x : T}
    (hx : IsHomogeneousTensor R M V e x) :
    tensorComponent R M V d (P • x) =
      if e ≤ d then component R M (d - e) P • x else 0 := by
  classical
  rw [tensorComponent_smul]
  by_cases hed : e ≤ d
  · simp only [hed, ↓reduceIte]
    calc
      _ = component R M (d - e) P • tensorComponent R M V e x := by
        apply Finset.sum_eq_single (d - e, e)
        · intro a ha hne
          have had := Finset.mem_antidiagonal.mp ha
          have hae : e ≠ a.2 := by
            intro h
            apply hne
            exact Prod.ext (by omega) h.symm
          simp only [tensorComponent_of_isHomogeneous R M V a.2 hx, hae,
            ↓reduceIte, smul_zero]
        · intro h
          exact (h (Finset.mem_antidiagonal.mpr (by omega))).elim
      _ = _ := by rw [hx]
  · simp only [hed, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro a ha
    have had := Finset.mem_antidiagonal.mp ha
    have hae : e ≠ a.2 := by omega
    simp only [tensorComponent_of_isHomogeneous R M V a.2 hx, hae,
      ↓reduceIte, smul_zero]

private theorem sum_range_components_mono (x : T) {a b : ℕ} (hab : a ≤ b)
    (hx : ∀ d, a < d → tensorComponent R M V d x = 0) :
    ∑ d ∈ Finset.range (b + 1), tensorComponent R M V d x =
      ∑ d ∈ Finset.range (a + 1), tensorComponent R M V d x := by
  apply (Finset.sum_subset (Finset.range_mono (by omega)) _).symm
  intro d hd hda
  apply hx d
  simp only [Finset.mem_range] at hda
  omega

/-- Every actual tensor has a finite canonical degree decomposition. -/
theorem exists_tensorComponent_bound (x : T) :
    ∃ D : ℕ, (∀ d, D < d → tensorComponent R M V d x = 0) ∧
      ∑ d ∈ Finset.range (D + 1), tensorComponent R M V d x = x := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul P v =>
    let D := (degreePolynomial R M P).natDegree
    have hz (d : ℕ) (hd : D < d) : component R M d P = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hd
    refine ⟨D, fun d hd => by simp only [tensorComponent_tmul, hz d hd,
      TensorProduct.zero_tmul], ?_⟩
    have hs : (degreePolynomial R M P).support ⊆ Finset.range (D + 1) := by
      intro d hd
      have hle := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hd)
      exact Finset.mem_range.mpr (by omega)
    have hsum : ∑ d ∈ Finset.range (D + 1), component R M d P = P := by
      calc
        _ = ∑ d ∈ (degreePolynomial R M P).support, component R M d P := by
          apply (Finset.sum_subset hs _).symm
          intro d hd hds
          exact Polynomial.notMem_support_iff.mp hds
        _ = P := sum_components R M P
    simpa only [tensorComponent_tmul, ← TensorProduct.sum_tmul] using
      congrArg (fun Q : S => Q ⊗ₜ[R] v) hsum
  | add x y hx hy =>
    obtain ⟨a, hax, hsumx⟩ := hx
    obtain ⟨b, hby, hsumy⟩ := hy
    refine ⟨max a b, ?_, ?_⟩
    · intro d hd
      simp only [map_add, hax d (by omega), hby d (by omega), add_zero]
    · simp only [map_add, Finset.sum_add_distrib,
        sum_range_components_mono R M V x (Nat.le_max_left a b) hax,
        sum_range_components_mono R M V y (Nat.le_max_right a b) hby, hsumx, hsumy]

variable {N : Type uN} {W : Type uW}
  [AddCommGroup N] [Module R N] [AddCommGroup W] [Module R W]

/-- Degree projection is natural for both tensor factors. -/
theorem tensorComponent_natural (f : M →ₗ[R] N) (g : V →ₗ[R] W) (d : ℕ) (x : T) :
    tensorComponent R N W d
        (TensorProduct.map
          (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp f)).toLinearMap g x) =
      TensorProduct.map
        (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp f)).toLinearMap g
        (tensorComponent R M V d x) := by
  induction x using TensorProduct.inductionOn with
  | tmul P v =>
    simp only [TensorProduct.map_tmul, tensorComponent_tmul, AlgHom.toLinearMap_apply,
      component_lift]
  | add x y hx hy => simp only [map_add, hx, hy]

end Langlands.Algebra.SymmetricGrading
