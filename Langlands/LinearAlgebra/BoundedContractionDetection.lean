import Langlands.LinearAlgebra.BoundedCreationContraction

/-! # Joint contraction detection and alternation in a bounded family -/

noncomputable section

universe u v w

namespace Langlands.LinearAlgebra.BoundedCreationContraction

variable {R : Type u} [CommRing R] {ι : Type v}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]

/-- All contractions of one positive-degree element, collected in a single linear map. -/
def jointContraction (d : ∀ (_ : ι) (n : ℕ), M (n + 1) →ₗ[R] M n) (n : ℕ) :
    M (n + 1) →ₗ[R] (ι → M n) :=
  LinearMap.pi fun i => d i n

section Relations

variable [Fintype ι] [DecidableEq ι]
  (c : ∀ (_ : ι) (n : ℕ), M n →ₗ[R] M (n + 1))
  (d : ∀ (_ : ι) (n : ℕ), M (n + 1) →ₗ[R] M n)
  (hrel : ∀ i j n,
    (d i (n + 1)).comp (c j (n + 1)) + (c j n).comp (d i n) =
      if i = j then LinearMap.id else 0)
  (hbound : ∀ n, Fintype.card ι < n → Subsingleton (M n))

include hrel hbound

/-- In positive degree, vanishing of every contraction forces the element to vanish. -/
theorem eq_zero_of_contractions_eq_zero (n : ℕ) (x : M (n + 1))
    (hx : ∀ i, d i n x = 0) : x = 0 := by
  have hm := mem_of_contractions_mem c d hrel (fun n => (⊥ : Submodule R (M n)))
    (by intro i n x hx; rw [Submodule.mem_bot] at hx ⊢; simp [hx])
    (by intro i n x hx; rw [Submodule.mem_bot] at hx ⊢; simp [hx])
    hbound Finset.univ n x
    (by intro i hi; simpa only [Submodule.mem_bot] using hx i)
    (by simp only [Finset.card_univ]; omega)
  simpa only [Submodule.mem_bot] using hm

/-- The whole family of positive-degree contractions is jointly injective. -/
theorem jointContraction_injective (n : ℕ) : Function.Injective (jointContraction d n) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply eq_zero_of_contractions_eq_zero c d hrel hbound n
  intro i
  have hi : d i n x = d i n y := congrFun hxy i
  rw [map_sub, hi, sub_self]

/-- The degree-zero creator/contraction formulas kill the square of each chosen creator. -/
theorem creator_square_eq_zero (v : ι → M 1)
    (hzero : ∀ i j, c j 0 (d i 0 (v j)) = if i = j then v j else 0) (j : ι) :
    c j 1 (v j) = 0 := by
  apply eq_zero_of_contractions_eq_zero c d hrel hbound 1
  intro i
  have he := LinearMap.congr_fun (hrel i j 0) (v j)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, hzero] at he
  by_cases hij : i = j
  · simpa only [ite_eq_left hij, LinearMap.id_apply, add_eq_right] using he
  · simpa only [ite_eq_right hij, LinearMap.zero_apply, add_zero] using he

/-- A skew bilinear degree-two product compatible with spanning creators is alternating,
including in characteristic two, if the degree-zero formulas hold. -/
theorem cup_self_eq_zero (B : M 1 →ₗ[R] M 1 →ₗ[R] M 2)
    (hskew : ∀ x y, B x y = -B y x) (v : ι → M 1)
    (hspan : Submodule.span R (Set.range v) = ⊤)
    (hcup : ∀ i x, c i 1 x = B (v i) x)
    (hzero : ∀ i j, c j 0 (d i 0 (v j)) = if i = j then v j else 0)
    (x : M 1) : B x x = 0 := by
  have hx : x ∈ Submodule.span R (Set.range v) := by rw [hspan]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [← hcup]
    exact creator_square_eq_zero c d hrel hbound v hzero i
  | zero => simp
  | add x y hx hy hxx hyy =>
    simp only [map_add, LinearMap.add_apply, hxx, hyy, zero_add, add_zero]
    rw [hskew x y, add_neg_cancel]
  | smul r x hx hxx =>
    simp only [map_smul, LinearMap.smul_apply, hxx, smul_zero]

end Relations

end Langlands.LinearAlgebra.BoundedCreationContraction
