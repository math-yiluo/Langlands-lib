import Mathlib.Algebra.Azumaya.Defs
import Mathlib.Algebra.Central.Basic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Nat.Sqrt

/-! Scalar extension of finite-dimensional central simple algebras. -/

noncomputable section

namespace Langlands.CentralSimple

universe uK uA uL

open scoped TensorProduct
open MulOpposite

variable (K : Type uK) [Field K] (A : Type uA) [Ring A] [Algebra K A]

attribute [local instance] instModuleTensorProductMop

@[simp] theorem enveloping_tmul_smul (a b x : A) :
    (a ⊗ₜ[K] op b) • x = a * x * b :=
  AlgHom.mulLeftRight_apply K A a (op b) x

/-- A simple ring is a simple module for its two-sided multiplication action. -/
theorem isSimpleModule_enveloping [IsSimpleRing A] :
    IsSimpleModule (A ⊗[K] Aᵐᵒᵖ) A := by
  have : Nontrivial (Submodule (A ⊗[K] Aᵐᵒᵖ) A) :=
    ⟨⟨⊥, ⊤, by
      intro h
      have : (1 : A) ∈ (⊥ : Submodule (A ⊗[K] Aᵐᵒᵖ) A) :=
        h ▸ Submodule.mem_top
      exact (one_ne_zero : (1 : A) ≠ 0) (by simpa only [Submodule.mem_bot] using this)⟩⟩
  apply (isSimpleModule_iff _ _).mpr
  refine ⟨fun N => ?_⟩
  let J : TwoSidedIdeal A := TwoSidedIdeal.mk' (N : Set A)
    N.zero_mem (fun hx hy => N.add_mem hx hy) (fun hx => N.neg_mem hx)
    (fun {x y} hy => by
      have hm := N.smul_mem (x ⊗ₜ[K] op (1 : A)) hy
      rw [enveloping_tmul_smul, mul_one] at hm
      exact hm)
    (fun {x y} hx => by
      have hm := N.smul_mem ((1 : A) ⊗ₜ[K] op y) hx
      rw [enveloping_tmul_smul, one_mul] at hm
      exact hm)
  rcases eq_bot_or_eq_top J with h | h
  · left
    ext x
    change x ∈ N ↔ x = 0
    have hx : x ∈ N ↔ x ∈ J := by simp [J]
    simpa [h] using hx
  · right
    ext x
    change x ∈ N ↔ True
    have hx : x ∈ N ↔ x ∈ J := by simp [J]
    simpa [h] using hx

/-- Every endomorphism of the two-sided regular module is a central scalar. -/
theorem envelopingEnd_eq_smul [Algebra.IsCentral K A]
    (g : Module.End (A ⊗[K] Aᵐᵒᵖ) A) :
    ∃ k : K, ∀ a : A, g a = k • a := by
  have hl (a : A) : g a = a * g 1 := by
    simpa only [enveloping_tmul_smul, mul_one, one_mul] using g.map_smul (a ⊗ₜ[K] op (1 : A)) (1 : A)
  have hr (a : A) : g a = g 1 * a := by
    simpa only [enveloping_tmul_smul, mul_one, one_mul] using g.map_smul ((1 : A) ⊗ₜ[K] op a) (1 : A)
  have hc : g 1 ∈ Subalgebra.center K A := by
    rw [Subalgebra.mem_center_iff]
    intro a
    exact (hl a).symm.trans (hr a)
  obtain ⟨k, hk⟩ := (Algebra.IsCentral.mem_center_iff K (D := A)).mp hc
  refine ⟨k, fun a => ?_⟩
  rw [hr a, hk, Algebra.smul_def]

/-- Two-sided multiplication spans every linear endomorphism of a finite CSA.
This derives the enveloping surjectivity from Jacobson density, without splitting. -/
theorem mulLeftRight_surjective [FiniteDimensional K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] : Function.Surjective (AlgHom.mulLeftRight K A) := by
  classical
  let := isSimpleModule_enveloping K A
  intro f
  let f' : Module.End (Module.End (A ⊗[K] Aᵐᵒᵖ) A) A :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun g a => by
        obtain ⟨k, hk⟩ := envelopingEnd_eq_smul K A g
        change f (g a) = g (f a)
        simp only [hk, map_smul] }
  let b := Module.finBasis K A
  obtain ⟨t, ht⟩ := jacobson_density f' (Finset.univ.image b)
  refine ⟨t, ?_⟩
  apply b.ext
  intro i
  exact (ht (b i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).symm

variable (L : Type uL) [Field L] [Algebra K L]

/-- Base extension of a pure two-sided multiplication is two-sided multiplication. -/
theorem baseChange_mulLeftRight_tmul (a b : A) (x : L ⊗[K] A) :
    ((AlgHom.mulLeftRight K A (a ⊗ₜ[K] op b)).baseChange L) x =
      (1 ⊗ₜ[K] a) * x * (1 ⊗ₜ[K] b) := by
  induction x using TensorProduct.inductionOn with
  | tmul l c => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_assoc]
  | add x y hx hy => simp [hx, hy, mul_add, add_mul]

/-- Every extended linear operator preserves two-sided ideals after field extension. -/
theorem baseChange_mem_ideal [FiniteDimensional K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] (f : Module.End K A) (J : TwoSidedIdeal (L ⊗[K] A))
    (x : L ⊗[K] A) (hx : x ∈ J) : f.baseChange L x ∈ J := by
  obtain ⟨t, rfl⟩ := mulLeftRight_surjective K A f
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [show b = op b.unop from (op_unop b).symm, baseChange_mulLeftRight_tmul]
    exact J.mul_mem_right _ _ (J.mul_mem_left _ _ hx)
  | add t s ht hs => simpa using J.add_mem ht hs

/-- Field extension preserves simplicity of a finite-dimensional central simple algebra. -/
theorem isSimpleRing_baseChange [FiniteDimensional K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] : IsSimpleRing (L ⊗[K] A) := by
  classical
  have : Nontrivial (L ⊗[K] A) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left K L A
      (algebraMap K A).injective
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro J
  rw [or_iff_not_imp_left, ← J.one_mem_iff]
  intro hJ
  obtain ⟨x, hxJ, hx0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hJ)
  have hx : x ≠ 0 := by simpa using hx0
  let b := Module.finBasis K A
  have hi : ∃ i, (b.baseChange L).repr x i ≠ 0 := by
    by_contra! h
    apply hx
    apply (b.baseChange L).repr.injective
    ext i
    simpa using h i
  obtain ⟨i, hi⟩ := hi
  let f : Module.End K A := (b.coord i).smulRight (1 : A)
  have hfx (z : L ⊗[K] A) : f.baseChange L z = ((b.baseChange L).repr z i) ⊗ₜ[K] (1 : A) := by
    induction z using TensorProduct.inductionOn with
    | tmul l a => simp [f, TensorProduct.tmul_smul, TensorProduct.smul_tmul]
    | add x y hx hy => simp [hx, hy, TensorProduct.add_tmul]
  have hm := baseChange_mem_ideal K A L f J x hxJ
  rw [hfx x] at hm
  have hm' := J.mul_mem_left (((b.baseChange L).repr x i)⁻¹ ⊗ₜ[K] (1 : A)) _ hm
  simpa [Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hi, ← Algebra.TensorProduct.one_def] using hm'

/-- On a central element, an extended two-sided operator acts by its value at one. -/
theorem baseChange_mulLeftRight_central (t : A ⊗[K] Aᵐᵒᵖ) (z : L ⊗[K] A)
    (hz : ∀ y : L ⊗[K] A, y * z = z * y) :
    ((AlgHom.mulLeftRight K A t).baseChange L) z =
      ((AlgHom.mulLeftRight K A t).baseChange L) 1 * z := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [show b = op b.unop from (op_unop b).symm]
    rw [baseChange_mulLeftRight_tmul, baseChange_mulLeftRight_tmul, mul_one]
    simpa only [mul_assoc] using
      congrArg (fun w => (1 ⊗ₜ[K] a) * w) (hz (1 ⊗ₜ[K] b.unop)).symm
  | add t s ht hs => simp [ht, hs, add_mul]

/-- Field extension preserves centrality of a finite-dimensional central simple algebra. -/
theorem isCentral_baseChange [FiniteDimensional K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] : Algebra.IsCentral L (L ⊗[K] A) := by
  classical
  refine ⟨fun z hz => ?_⟩
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : A) ≠ 0)
  let F : Module.End K A := f.smulRight (1 : A)
  have hF1 : F.baseChange L (1 : L ⊗[K] A) = 1 := by
    rw [Algebra.TensorProduct.one_def, LinearMap.baseChange_tmul]
    simp [F, hf, ← Algebra.TensorProduct.one_def]
  have hFz : F.baseChange L z = z := by
    obtain ⟨t, ht⟩ := mulLeftRight_surjective K A F
    have he := baseChange_mulLeftRight_central K A L t z
      ((Subalgebra.mem_center_iff.mp hz))
    simpa only [ht, hF1, one_mul] using he
  have scalar (w : L ⊗[K] A) : ∃ c : L, F.baseChange L w = c ⊗ₜ[K] (1 : A) := by
    induction w using TensorProduct.inductionOn with
    | tmul l a =>
      refine ⟨f a • l, ?_⟩
      simp [F, TensorProduct.tmul_smul, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨c + d, by simp [hc, hd, TensorProduct.add_tmul]⟩
  obtain ⟨c, hc⟩ := scalar z
  rw [Algebra.mem_bot]
  exact ⟨c, by rw [← hFz, hc]; rfl⟩

/-- A finite CSA admits a full matrix chart over any algebraically closed extension. -/
theorem exists_matrix_chart [IsAlgClosed L] [FiniteDimensional K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] :
    ∃ (n : ℕ) (_ : NeZero n),
      Nonempty ((L ⊗[K] A) ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by
  have := isSimpleRing_baseChange K A L
  exact IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed L (L ⊗[K] A)

/-- Dimension bookkeeping for any splitting chart, with no closure assumption. -/
theorem finrank_eq_matrix_size (n : ℕ)
    (e : (L ⊗[K] A) ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    Module.finrank K A = n * n := by
  calc
    Module.finrank K A = Module.finrank L (L ⊗[K] A) := Module.finrank_baseChange.symm
    _ = Module.finrank L (Matrix (Fin n) (Fin n) L) := e.toLinearEquiv.finrank_eq
    _ = n * n := by simp [Module.finrank_matrix]

/-- The reduced degree is the natural square root of the vector-space dimension. -/
def reducedDegree : ℕ := Nat.sqrt (Module.finrank K A)

/-- Reduced degree is unchanged under field extension. -/
theorem reducedDegree_baseChange :
    reducedDegree L (L ⊗[K] A) = reducedDegree K A := by
  simp [reducedDegree]

/-- A splitting chart necessarily has the reduced degree as its matrix size. -/
theorem matrix_size_eq_reducedDegree (n : ℕ)
    (e : (L ⊗[K] A) ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    n = reducedDegree K A := by
  rw [reducedDegree, finrank_eq_matrix_size K A L n e, Nat.sqrt_eq]

/-- The reduced degree of a finite CSA is positive. -/
theorem reducedDegree_pos [FiniteDimensional K A] [IsSimpleRing A] :
    0 < reducedDegree K A := by
  rw [reducedDegree, Nat.sqrt_pos]
  exact Module.finrank_pos

instance reducedDegree_neZero [FiniteDimensional K A] [IsSimpleRing A] :
    NeZero (reducedDegree K A) :=
  ⟨Nat.ne_of_gt (reducedDegree_pos K A)⟩

/-- The dimension of a finite CSA is the square of its reduced degree. -/
theorem finrank_eq_reducedDegree_mul_self [FiniteDimensional K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] :
    Module.finrank K A = reducedDegree K A * reducedDegree K A := by
  obtain ⟨n, _, ⟨e⟩⟩ := exists_matrix_chart K A (AlgebraicClosure K)
  have hd := finrank_eq_matrix_size K A (AlgebraicClosure K) n e
  simp [reducedDegree, hd, Nat.sqrt_eq]

/-- An algebraically closed extension splits a finite CSA at its reduced degree. -/
theorem exists_matrix_chart_reducedDegree [IsAlgClosed L] [FiniteDimensional K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] :
    Nonempty ((L ⊗[K] A) ≃ₐ[L]
      Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L) := by
  obtain ⟨n, _, ⟨e⟩⟩ := exists_matrix_chart K A L
  rw [← matrix_size_eq_reducedDegree K A L n e]
  exact ⟨e⟩

/-- A chosen actual splitting chart over the algebraic closure. -/
def algebraicClosureChart [FiniteDimensional K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] : (AlgebraicClosure K ⊗[K] A) ≃ₐ[AlgebraicClosure K]
      Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) (AlgebraicClosure K) :=
  (exists_matrix_chart_reducedDegree K A (AlgebraicClosure K)).some

end Langlands.CentralSimple
