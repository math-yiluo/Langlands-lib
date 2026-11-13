import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Tensor evaluation for a generator with kernels of elements

Let `C` be a preadditive category with finite biproducts, together with an
additive "underlying group" assignment `V` (an abelian group `V X` for every
object and an additive map `u f : V X →+ V Y` for every morphism, compatible
with identities, composition and addition of morphisms). Let `P` be an object
such that

* every element of every `V X` is a finite sum of elements `± u α w` with
  `α : P ⟶ X` and `w : V P` (`P` generates elementwise), and
* every element of `V X` killed by `u f` comes from an element of an object `K`
  through a morphism `ι : K ⟶ X` with `ι ≫ f = 0` (elementwise kernels).

Then for every object `Y` the `ℤ`-linear evaluation
`(P ⟶ Y) ⊗[ℤ] V P → V Y`, `α ⊗ w ↦ u α w`, is surjective and its kernel is
the span of the balancing elements `(r ≫ α) ⊗ w - α ⊗ u r w`, `r : End P`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe w v u

namespace Langlands.Renard

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (V : C → Type w) [∀ X, AddCommGroup (V X)]
  (u : ∀ {X Y : C}, (X ⟶ Y) → V X →+ V Y)

/-- The span of the balancing elements `(r ≫ α) ⊗ w - α ⊗ u r w`. -/
def tensorEvaluationBalancing (P Y : C) : Submodule ℤ ((P ⟶ Y) ⊗[ℤ] V P) :=
  Submodule.span ℤ (Set.range
    (fun p : End P × (P ⟶ Y) × V P =>
      (p.1 ≫ p.2.1) ⊗ₜ[ℤ] p.2.2 - p.2.1 ⊗ₜ[ℤ] u p.1 p.2.2))

variable {V u}

/-- The `ℤ`-bilinear evaluation pairing `(α, w) ↦ u α w`. -/
def tensorEvaluationPairing
    (hadd : ∀ {X Y : C} (f g : X ⟶ Y) (x : V X), u (f + g) x = u f x + u g x)
    (P Y : C) : (P ⟶ Y) →ₗ[ℤ] V P →ₗ[ℤ] V Y :=
  LinearMap.mk₂ ℤ (fun α w => u α w)
    (fun f g x => hadd f g x)
    (fun n f x => by
      have h : (AddMonoidHom.mk' (fun g : P ⟶ Y => u g x) (fun f g => hadd f g x)) (n • f) =
          n • (AddMonoidHom.mk' (fun g : P ⟶ Y => u g x) (fun f g => hadd f g x)) f :=
        map_zsmul _ n f
      exact h)
    (fun f x y => map_add (u f) x y)
    (fun n f x => map_zsmul (u f) n x)

/-- The `ℤ`-linear evaluation `(P ⟶ Y) ⊗[ℤ] V P → V Y`, `α ⊗ w ↦ u α w`. -/
def tensorEvaluation
    (hadd : ∀ {X Y : C} (f g : X ⟶ Y) (x : V X), u (f + g) x = u f x + u g x)
    (P Y : C) : (P ⟶ Y) ⊗[ℤ] V P →ₗ[ℤ] V Y :=
  TensorProduct.lift (tensorEvaluationPairing hadd P Y)

@[simp]
theorem tensorEvaluation_tmul
    (hadd : ∀ {X Y : C} (f g : X ⟶ Y) (x : V X), u (f + g) x = u f x + u g x)
    {P Y : C} (α : P ⟶ Y) (w : V P) :
    tensorEvaluation hadd P Y (α ⊗ₜ w) = u α w :=
  TensorProduct.lift.tmul _ _

variable (hid : ∀ (X : C) (x : V X), u (𝟙 X) x = x)
  (hcomp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (x : V X), u (f ≫ g) x = u g (u f x))
  (hadd : ∀ {X Y : C} (f g : X ⟶ Y) (x : V X), u (f + g) x = u f x + u g x)

include hcomp in
/-- The balancing elements lie in the kernel of the evaluation. -/
theorem tensorEvaluationBalancing_le_ker (P Y : C) :
    tensorEvaluationBalancing V u P Y ≤ LinearMap.ker (tensorEvaluation hadd P Y) := by
  rw [tensorEvaluationBalancing, Submodule.span_le]
  rintro _ ⟨⟨r, α, w⟩, rfl⟩
  simp [hcomp]

omit [Preadditive C] in
/-- An additive map out of `V K` lands in an additive subgroup once it does on the
generating elements `u β w`. -/
theorem map_mem_of_generator {P K : C} {M : Type*} [AddCommGroup M] (S : AddSubgroup M)
    (Φ : V K →+ M)
    (hgen : ∀ x : V K, x ∈ AddSubgroup.closure {y | ∃ (β : P ⟶ K) (w : V P), u β w = y})
    (hΦ : ∀ (β : P ⟶ K) (w : V P), Φ (u β w) ∈ S) (x : V K) : Φ x ∈ S := by
  have hle : AddSubgroup.closure {y | ∃ (β : P ⟶ K) (w : V P), u β w = y} ≤ S.comap Φ := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨β, w, rfl⟩
    exact hΦ β w
  exact hle (hgen x)

include hid hcomp in
/-- **Tensor evaluation.** If `P` generates every object elementwise and kernels exist
elementwise, the evaluation `(P ⟶ Y) ⊗[ℤ] V P → V Y` is surjective with kernel the
span of the balancing elements. -/
theorem tensorEvaluation_surjective_and_ker [HasFiniteBiproducts C] (P Y : C)
    (hgen : ∀ (X : C) (x : V X),
      x ∈ AddSubgroup.closure {y | ∃ (α : P ⟶ X) (w : V P), u α w = y})
    (hker : ∀ {X Z : C} (f : X ⟶ Z) (x : V X), u f x = 0 →
      ∃ (K : C) (ι : K ⟶ X) (k : V K), u ι k = x ∧ ι ≫ f = 0) :
    Function.Surjective (tensorEvaluation hadd P Y) ∧
      LinearMap.ker (tensorEvaluation hadd P Y) = tensorEvaluationBalancing V u P Y := by
  classical
  refine ⟨fun y => ?_, ?_⟩
  · -- Surjectivity: the generating elements lie in the range.
    have hle : AddSubgroup.closure {y | ∃ (α : P ⟶ Y) (w : V P), u α w = y} ≤
        (LinearMap.range (tensorEvaluation hadd P Y)).toAddSubgroup := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨α, w, rfl⟩
      exact ⟨α ⊗ₜ w, tensorEvaluation_tmul hadd α w⟩
    exact hle (hgen Y y)
  refine le_antisymm (fun x hx => ?_) (tensorEvaluationBalancing_le_ker hcomp hadd P Y)
  rw [LinearMap.mem_ker] at hx
  -- Write `x` as a sum over `Fin n` of pure tensors.
  obtain ⟨n, e, rfl⟩ : ∃ (n : ℕ) (e : Fin n → (P ⟶ Y) × V P),
      x = ∑ i, (e i).1 ⊗ₜ[ℤ] (e i).2 := by
    obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
    refine ⟨S.card, fun i => (S.equivFin.symm i).1, ?_⟩
    rw [← Finset.sum_coe_sort S, ← Equiv.sum_comp S.equivFin.symm]
  -- The biproduct of copies of `P` indexed by the terms of `x`.
  let B : Fin n → C := fun _ => P
  let φ : ⨁ B ⟶ Y := biproduct.desc (fun s => (e s).1)
  let y : V (⨁ B) := ∑ s, u (biproduct.ι B s) (e s).2
  have hy : u φ y = 0 := by
    rw [← hx]
    simp only [y, map_sum, ← hcomp, φ, biproduct.ι_desc, tensorEvaluation_tmul]
  obtain ⟨K, ι, k, hk, hιφ⟩ := hker φ y hy
  -- The comparison map from `V K` back to the tensor product.
  let Φ : V K →+ (P ⟶ Y) ⊗[ℤ] V P :=
    ∑ s, (TensorProduct.mk ℤ (P ⟶ Y) (V P) (e s).1).toAddMonoidHom.comp
      (u (ι ≫ biproduct.π B s))
  have hΦ : ∀ k' : V K, Φ k' = ∑ s, (e s).1 ⊗ₜ u (ι ≫ biproduct.π B s) k' := by
    intro k'
    simp [Φ]
  -- `Φ k` recovers the original tensor.
  have hΦk : Φ k = ∑ i, (e i).1 ⊗ₜ[ℤ] (e i).2 := by
    rw [hΦ]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [hcomp, hk]
    simp only [y, map_sum, ← hcomp]
    rw [Finset.sum_eq_single s]
    · rw [biproduct.ι_π_self, hid]
    · intro t _ hts
      rw [biproduct.ι_π_ne B hts]
      have h0 : u (0 : P ⟶ P) (e t).2 = 0 := by
        have := hadd (0 : P ⟶ P) 0 (e t).2
        rw [add_zero] at this
        exact left_eq_add.mp this
      exact h0
    · intro h
      exact absurd (Finset.mem_univ s) h
  rw [← hΦk]
  -- Every value of `Φ` is balanced.
  refine map_mem_of_generator (tensorEvaluationBalancing V u P Y).toAddSubgroup Φ (hgen K) ?_ k
  intro β w'
  let r : Fin n → End P := fun s => β ≫ ι ≫ biproduct.π B s
  have hsum : ∑ s, r s ≫ (e s).1 = 0 := by
    have : β ≫ ι ≫ φ = ∑ s, r s ≫ (e s).1 := by
      simp only [φ, r]
      rw [biproduct.desc_eq, Preadditive.comp_sum, Preadditive.comp_sum]
      simp only [Category.assoc]
    rw [← this, hιφ, Limits.comp_zero]
  have hrewrite : Φ (u β w') = -∑ s,
      ((r s ≫ (e s).1) ⊗ₜ[ℤ] w' - (e s).1 ⊗ₜ[ℤ] u (r s) w') := by
    rw [Finset.sum_sub_distrib, ← TensorProduct.sum_tmul, hsum, TensorProduct.zero_tmul,
      zero_sub, neg_neg, hΦ]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [r, hcomp]
  rw [hrewrite]
  refine (tensorEvaluationBalancing V u P Y).toAddSubgroup.neg_mem
    ((tensorEvaluationBalancing V u P Y).toAddSubgroup.sum_mem fun s _ => ?_)
  exact Submodule.subset_span ⟨⟨r s, (e s).1, w'⟩, rfl⟩

include hid hcomp hadd in
/-- Existential packaging of `tensorEvaluation_surjective_and_ker`. -/
theorem exists_tensorEvaluation [HasFiniteBiproducts C] (P Y : C)
    (hgen : ∀ (X : C) (x : V X),
      x ∈ AddSubgroup.closure {y | ∃ (α : P ⟶ X) (w : V P), u α w = y})
    (hker : ∀ {X Z : C} (f : X ⟶ Z) (x : V X), u f x = 0 →
      ∃ (K : C) (ι : K ⟶ X) (k : V K), u ι k = x ∧ ι ≫ f = 0) :
    ∃ ev : (P ⟶ Y) ⊗[ℤ] V P →ₗ[ℤ] V Y,
      (∀ (α : P ⟶ Y) (w : V P), ev (α ⊗ₜ w) = u α w) ∧
      Function.Surjective ev ∧
      LinearMap.ker ev = Submodule.span ℤ (Set.range
        (fun p : End P × (P ⟶ Y) × V P =>
          (p.1 ≫ p.2.1) ⊗ₜ[ℤ] p.2.2 - p.2.1 ⊗ₜ[ℤ] u p.1 p.2.2)) :=
  ⟨tensorEvaluation hadd P Y, fun α w => tensorEvaluation_tmul hadd α w,
    tensorEvaluation_surjective_and_ker hid hcomp hadd P Y hgen hker⟩

end Langlands.Renard
