import Langlands.AlgebraicGeometry.CechKunnethStatement

/-!
# Künneth detection of products of degree-one Čech cocycles

This file proves `Langlands.Cohomology.Cech.KunnethDetectionStatement`.
-/

universe w w' u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

namespace Langlands.Cohomology.Cech

namespace KunnethDetection

section Combinatorics

/-- `step s j = 0` for `j < s` and `step s j = 1` otherwise. -/
def step {m : ℕ} (s : ℕ) : Fin m → Fin 2 := fun j => if (j : ℕ) < s then 0 else 1

/-- The degeneracy `j ↦ j` for `j ≤ s` and `j ↦ j - 1` for `j > s` (clamped to `m`). -/
def degen {m : ℕ} (s : ℕ) : Fin (m + 2) → Fin (m + 1) := fun j =>
  ⟨if (j : ℕ) ≤ s then min (j : ℕ) m else (j : ℕ) - 1, by have := j.isLt; split_ifs <;> omega⟩

/-- The face map `j ↦ j` for `j < k` and `j ↦ j + 1` for `j ≥ k`. -/
def skip {m : ℕ} (k : ℕ) : Fin m → Fin (m + 1) := fun j =>
  ⟨if (j : ℕ) < k then (j : ℕ) else (j : ℕ) + 1, by have := j.isLt; split_ifs <;> omega⟩

lemma val_step {m : ℕ} (s : ℕ) (j : Fin m) :
    ((step s j : Fin 2) : ℕ) = if (j : ℕ) < s then 0 else 1 := by
  unfold step
  split_ifs <;> rfl

lemma val_degen {m : ℕ} (s : ℕ) (j : Fin (m + 2)) :
    ((degen s j : Fin (m + 1)) : ℕ) = if (j : ℕ) ≤ s then min (j : ℕ) m else (j : ℕ) - 1 :=
  rfl

lemma val_skip {m : ℕ} (k : ℕ) (j : Fin m) :
    ((skip k j : Fin (m + 1)) : ℕ) = if (j : ℕ) < k then (j : ℕ) else (j : ℕ) + 1 :=
  rfl

lemma succAbove_eq_skip {m : ℕ} (k : Fin (m + 1)) : k.succAbove = skip (k : ℕ) := by
  funext j
  apply Fin.ext
  rw [val_skip]
  by_cases h : (j : ℕ) < k
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.2 h), Fin.val_castSucc]
    simp [h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.le_def.2 (by simp; omega)), Fin.val_succ]
    simp [h]

lemma fin_two_funext {α : Sort*} {f g : Fin 2 → α} (h₀ : f 0 = g 0) (h₁ : f 1 = g 1) :
    f = g := by
  funext a
  fin_cases a
  exacts [h₀, h₁]

lemma step_comp_edge_self {m : ℕ} (s : Fin (m + 1)) :
    (step ((s : ℕ) + 1) : Fin (m + 2) → Fin 2) ∘ edge s = id := by
  refine fin_two_funext (Fin.ext ?_) (Fin.ext ?_) <;>
    simp only [Function.comp_apply, edge_zero, edge_one, val_step, Fin.val_castSucc, Fin.val_succ,
      id_eq, Fin.val_zero, Fin.val_one] <;>
    split_ifs <;> omega

lemma degen_comp_edge_self {m : ℕ} (s : Fin (m + 1)) :
    (degen (s : ℕ) : Fin (m + 2) → Fin (m + 1)) ∘ edge s = fun _ => s := by
  have := s.isLt
  refine fin_two_funext (Fin.ext ?_) (Fin.ext ?_) <;>
    simp only [Function.comp_apply, edge_zero, edge_one, val_degen, Fin.val_castSucc,
      Fin.val_succ] <;>
    split_ifs <;> omega

lemma step_comp_edge_succAbove {m : ℕ} (s : Fin (m + 1)) (k : Fin m) :
    (step ((s : ℕ) + 1) : Fin (m + 2) → Fin 2) ∘ edge (s.succAbove k) =
      fun _ => step ((s : ℕ) + 1) (edge (s.succAbove k) 0) := by
  rw [succAbove_eq_skip]
  refine fin_two_funext (Fin.ext ?_) (Fin.ext ?_)
  all_goals simp only [Function.comp_apply, edge_zero, edge_one, val_step, Fin.val_castSucc,
    Fin.val_succ, val_skip]
  all_goals split_ifs <;> omega

lemma degen_comp_edge_succAbove {m : ℕ} (s : Fin (m + 1)) (k : Fin m) :
    (degen (s : ℕ) : Fin (m + 2) → Fin (m + 1)) ∘ edge (s.succAbove k) = edge k := by
  have := s.isLt
  have := k.isLt
  rw [succAbove_eq_skip]
  refine fin_two_funext (Fin.ext ?_) (Fin.ext ?_) <;>
    simp only [Function.comp_apply, edge_zero, edge_one, val_degen, Fin.val_castSucc,
      Fin.val_succ, val_skip] <;>
    split_ifs <;> omega

lemma step_comp_skip_of_le {m : ℕ} {s k : ℕ} (h : k ≤ s) :
    (step (s + 1) : Fin (m + 1) → Fin 2) ∘ skip k = step s := by
  funext j
  apply Fin.ext
  simp only [Function.comp_apply, val_step, val_skip]
  split_ifs <;> omega

lemma step_comp_skip_of_lt {m : ℕ} {s k : ℕ} (h : s + 1 < k) :
    (step (s + 1) : Fin (m + 1) → Fin 2) ∘ skip k = step (s + 1) := by
  funext j
  apply Fin.ext
  simp only [Function.comp_apply, val_step, val_skip]
  split_ifs <;> omega

lemma step_comp_skip_succ {m : ℕ} (s : ℕ) :
    (step (s + 1) : Fin (m + 1) → Fin 2) ∘ skip (s + 1) = step (s + 1) := by
  funext j
  apply Fin.ext
  simp only [Function.comp_apply, val_step, val_skip]
  split_ifs <;> omega

lemma degen_comp_skip_of_lt {m : ℕ} {s k : ℕ} (hk : k < s) (hs : s ≤ m + 1) :
    (degen s : Fin (m + 3) → Fin (m + 2)) ∘ skip k = skip k ∘ (degen (s - 1) : Fin (m + 2) → _) := by
  funext j
  apply Fin.ext
  have := j.isLt
  simp only [Function.comp_apply, val_degen, val_skip]
  split_ifs <;> omega

lemma degen_comp_skip_self {m : ℕ} (s : ℕ) :
    (degen s : Fin (m + 3) → Fin (m + 2)) ∘ skip s = id := by
  funext j
  apply Fin.ext
  have := j.isLt
  simp only [Function.comp_apply, val_degen, val_skip, id]
  split_ifs <;> omega

lemma degen_comp_skip_succ {m : ℕ} (s : ℕ) :
    (degen s : Fin (m + 3) → Fin (m + 2)) ∘ skip (s + 1) = id := by
  funext j
  apply Fin.ext
  have := j.isLt
  simp only [Function.comp_apply, val_degen, val_skip, id]
  split_ifs <;> omega

lemma degen_comp_skip_of_gt {m : ℕ} {s k : ℕ} (hk : s + 1 < k) (hk' : k ≤ m + 2) :
    (degen s : Fin (m + 3) → Fin (m + 2)) ∘ skip k =
      skip (k - 1) ∘ (degen s : Fin (m + 2) → Fin (m + 1)) := by
  funext j
  apply Fin.ext
  have := j.isLt
  simp only [Function.comp_apply, val_degen, val_skip]
  split_ifs <;> omega

/-- The sign bookkeeping of the shuffle map: the double sum of `F` splits into the boundary
terms `Q` and the double sum of `H`. -/
lemma shuffle_sum {A : Type*} [AddCommGroup A] (F H : ℕ → ℕ → A) (Q : ℕ → A) (N : ℕ)
    (h₁ : ∀ s k, k < s → s ≤ N → F s k = H (s - 1) k)
    (h₂ : ∀ s, s ≤ N → F s s = Q s)
    (h₃ : ∀ s, s ≤ N → F s (s + 1) = Q (s + 1))
    (h₄ : ∀ s k, s + 1 < k → k ≤ N + 1 → F s k = H s (k - 1)) :
    ∑ s ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 2), (-1 : ℤ) ^ (s + k) • F s k =
      Q 0 - Q (N + 1) -
        ∑ t ∈ Finset.range N, ∑ j ∈ Finset.range (N + 1), (-1 : ℤ) ^ (t + j) • H t j := by
  induction N with
  | zero =>
    simp [Finset.sum_range_succ, h₂ 0 le_rfl, h₃ 0 le_rfl, sub_eq_add_neg]
  | succ N ih =>
    have ih' := ih (fun s k hk hs => h₁ s k hk (by omega)) (fun s hs => h₂ s (by omega))
      (fun s hs => h₃ s (by omega)) (fun s k hk hk' => h₄ s k hk (by omega))
    have e₁ : ∑ s ∈ Finset.range (N + 1 + 1), ∑ k ∈ Finset.range (N + 1 + 2),
        (-1 : ℤ) ^ (s + k) • F s k =
        ∑ s ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 2), (-1 : ℤ) ^ (s + k) • F s k +
          ∑ s ∈ Finset.range (N + 1), (-1 : ℤ) ^ (s + (N + 2)) • F s (N + 2) +
          (∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ (N + 1 + k) • F (N + 1) k +
            (-1 : ℤ) ^ (N + 1 + (N + 1)) • F (N + 1) (N + 1) +
            (-1 : ℤ) ^ (N + 1 + (N + 2)) • F (N + 1) (N + 2)) := by
      rw [Finset.sum_range_succ _ (N + 1), show N + 1 + 2 = N + 2 + 1 by ring,
        Finset.sum_range_succ _ (N + 2), Finset.sum_range_succ _ (N + 1)]
      rw [← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_range_succ]
    have e₂ : ∑ t ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1 + 1),
        (-1 : ℤ) ^ (t + j) • H t j =
        ∑ t ∈ Finset.range N, ∑ j ∈ Finset.range (N + 1), (-1 : ℤ) ^ (t + j) • H t j +
          ∑ t ∈ Finset.range (N + 1), (-1 : ℤ) ^ (t + (N + 1)) • H t (N + 1) +
          ∑ j ∈ Finset.range (N + 1), (-1 : ℤ) ^ (N + j) • H N j := by
      simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
      abel
    have f₁ : ∑ s ∈ Finset.range (N + 1), (-1 : ℤ) ^ (s + (N + 2)) • F s (N + 2) =
        -∑ s ∈ Finset.range (N + 1), (-1 : ℤ) ^ (s + (N + 1)) • H s (N + 1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [Finset.mem_range] at hs
      rw [h₄ s (N + 2) (by omega) le_rfl, show N + 2 - 1 = N + 1 by omega,
        show s + (N + 2) = s + (N + 1) + 1 by ring, pow_succ, mul_neg_one, neg_smul]
    have f₂ : ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ (N + 1 + k) • F (N + 1) k =
        -∑ j ∈ Finset.range (N + 1), (-1 : ℤ) ^ (N + j) • H N j := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [h₁ (N + 1) k (by omega) le_rfl, show N + 1 - 1 = N by omega,
        show N + 1 + k = N + k + 1 by ring, pow_succ, mul_neg_one, neg_smul]
    have f₃ : (-1 : ℤ) ^ (N + 1 + (N + 1)) • F (N + 1) (N + 1) = Q (N + 1) := by
      rw [h₂ (N + 1) le_rfl, ← two_mul, pow_mul]
      simp
    have f₄ : (-1 : ℤ) ^ (N + 1 + (N + 2)) • F (N + 1) (N + 2) = -Q (N + 1 + 1) := by
      rw [h₃ (N + 1) le_rfl, show N + 1 + (N + 2) = 2 * (N + 1) + 1 by ring, pow_succ, pow_mul]
      simp
    rw [e₁, e₂, ih', f₁, f₂, f₃, f₄]
    abel

end Combinatorics

section Slant

open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ πX πY)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)
  {ι : Type w} [Finite ι] (U : ι → X.Opens) (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R)

/-- The bijection `(∏_σ Γ(X, U_σ)) ⊗[R] Γ(Y, W) ≃ ∏_σ Γ(P, p₁⁻¹ U_σ ⊓ p₂⁻¹ W)` for an affine
open `W`, with the second factor written as a product over `Unit`. -/
noncomputable def tensorEquiv (W : Y.Opens) (hW : IsAffineOpen W) :
    (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) ⊗[R] (∀ _ : Unit, Γ(Y, W)) ≃+
      ∀ (σ : Fin 2 → ι) (_ : Unit), Γ(P, prodOpen p₁ p₂ (inter U σ) W) :=
  AddEquiv.ofBijective
    (tensorFam halgX halgY hP (fun σ : Fin 2 → ι => inter U σ) (fun _ : Unit => W))
    (tensorFam_bijective halgX halgY hP _ _ hU fun _ => hW)

/-- The slant product with `l`: it sends `p₁^* x * p₂^* y` to `l x • y`. -/
noncomputable def slant (W : Y.Opens) (hW : IsAffineOpen W) :
    (∀ σ : Fin 2 → ι, Γ(P, prodOpen p₁ p₂ (inter U σ) W)) →+ Γ(Y, W) where
  toFun F := TensorProduct.lid R Γ(Y, W) (TensorProduct.map l (LinearMap.proj ())
    ((tensorEquiv hP halgX halgY U hU W hW).symm fun σ _ => F σ))
  map_zero' := by
    rw [show (fun (σ : Fin 2 → ι) (_ : Unit) =>
      (0 : ∀ σ : Fin 2 → ι, Γ(P, prodOpen p₁ p₂ (inter U σ) W)) σ) = 0 from rfl,
      map_zero, map_zero, map_zero]
  map_add' F G := by
    rw [show (fun σ (_ : Unit) => (F + G) σ) = (fun σ _ => F σ) + (fun σ _ => G σ) from rfl,
      map_add, map_add, map_add]

lemma slant_tensorFam (W : Y.Opens) (hW : IsAffineOpen W)
    (t : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) ⊗[R] (∀ _ : Unit, Γ(Y, W))) :
    slant hP halgX halgY U hU l W hW (fun σ => tensorFam halgX halgY hP
        (fun σ : Fin 2 → ι => inter U σ) (fun _ : Unit => W) t σ ()) =
      TensorProduct.lid R Γ(Y, W) (TensorProduct.map l (LinearMap.proj ()) t) := by
  change TensorProduct.lid R Γ(Y, W) (TensorProduct.map l (LinearMap.proj ())
    ((tensorEquiv hP halgX halgY U hU W hW).symm (tensorEquiv hP halgX halgY U hU W hW t))) = _
  rw [AddEquiv.symm_apply_apply]

lemma slant_mul (W : Y.Opens) (hW : IsAffineOpen W) (x : ∀ σ : Fin 2 → ι, Γ(X, inter U σ))
    (y : Γ(Y, W)) :
    slant hP halgX halgY U hU l W hW (fun σ =>
      (p₁.appLE (inter U σ) (prodOpen p₁ p₂ (inter U σ) W) inf_le_left).hom (x σ) *
        (p₂.appLE W (prodOpen p₁ p₂ (inter U σ) W) inf_le_right).hom y) = l x • y := by
  have h := slant_tensorFam hP halgX halgY U hU l W hW (x ⊗ₜ fun _ => y)
  simp only [tensorFam_tmul, TensorProduct.map_tmul, TensorProduct.lid_tmul,
    LinearMap.proj_apply] at h
  exact h

lemma slant_res {W W' : Y.Opens} (h : W' ≤ W) (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
    (F : ∀ σ : Fin 2 → ι, Γ(P, prodOpen p₁ p₂ (inter U σ) W)) :
    res (P := ab Y.presheaf) h (slant hP halgX halgY U hU l W hW F) =
      slant hP halgX halgY U hU l W' hW'
        (fun σ => res (P := ab P.presheaf) (prodOpen_mono le_rfl h) (F σ)) := by
  obtain ⟨t, ht⟩ := (tensorEquiv hP halgX halgY U hU W hW).surjective fun σ _ => F σ
  have hF : F = fun σ => tensorFam halgX halgY hP (fun σ : Fin 2 → ι => inter U σ)
      (fun _ : Unit => W) t σ () := funext fun σ => (congrFun (congrFun ht σ) ()).symm
  have hF' : (fun σ => res (P := ab P.presheaf) (prodOpen_mono le_rfl h) (F σ)) =
      fun σ => tensorFam halgX halgY hP (fun σ : Fin 2 → ι => inter U σ) (fun _ : Unit => W')
        ((resPi πY halgY (fun _ : Unit => W) (fun _ : Unit => W') id fun _ => h).lTensor _ t)
          σ () := by
    funext σ
    rw [tensorFam_lTensor_resPi, hF]
    rfl
  rw [hF', slant_tensorFam, hF, slant_tensorFam]
  clear hF' hF ht
  induction t with
  | tmul x y =>
    simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, TensorProduct.lid_tmul,
      LinearMap.proj_apply, resPi_apply]
    exact (resAlgHom πY halgY h).toLinearMap.map_smul (l x) (y ())
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Finite ι] in
lemma inter_fin_one (τ : Fin 1 → ι) : inter U τ = inter U (τ ∘ fun _ : Fin 2 => 0) := by
  refine le_antisymm (inter_le_comp τ _) ((inter_le_comp _ (fun _ : Fin 1 => 0)).trans
    (le_of_eq (congrArg (inter U) ?_)))
  funext a
  rw [Fin.fin_one_eq_zero a]
  rfl

omit [Finite ι] in
include hU in
lemma isAffineOpen_inter_one (τ : Fin 1 → ι) : IsAffineOpen (inter U τ) := by
  rw [inter_fin_one U τ]
  exact hU _

/-- The slant product kills the Čech coboundary in the first factor. -/
lemma slant_coboundary (hl : ∀ y : C (ab X.presheaf) U 0, l (d (ab X.presheaf) U 0 y) = 0)
    (W : Y.Opens) (hW : IsAffineOpen W)
    (G : ∀ τ : Fin 1 → ι, Γ(P, prodOpen p₁ p₂ (inter U τ) W)) :
    slant hP halgX halgY U hU l W hW (fun σ =>
      res (P := ab P.presheaf) (prodOpen_mono (inter_le_comp σ (Fin.succAbove 0)) le_rfl)
          (G (σ ∘ Fin.succAbove 0)) -
        res (P := ab P.presheaf) (prodOpen_mono (inter_le_comp σ (Fin.succAbove 1)) le_rfl)
          (G (σ ∘ Fin.succAbove 1))) = 0 := by
  obtain ⟨t, ht⟩ := (tensorFam_bijective halgX halgY hP (fun τ : Fin 1 → ι => inter U τ)
    (fun _ : Unit => W) (isAffineOpen_inter_one U hU) fun _ => hW).2 fun τ _ => G τ
  have hG : ∀ τ, G τ = tensorFam halgX halgY hP (fun τ : Fin 1 → ι => inter U τ)
      (fun _ : Unit => W) t τ () := fun τ => (congrFun (congrFun ht τ) ()).symm
  let r : Fin 2 → (∀ τ : Fin 1 → ι, Γ(X, inter U τ)) →ₗ[R] ∀ σ : Fin 2 → ι, Γ(X, inter U σ) :=
    fun k => resPi πX halgX (fun τ : Fin 1 → ι => inter U τ) (fun σ : Fin 2 → ι => inter U σ)
      (fun σ => σ ∘ k.succAbove) (fun σ => inter_le_comp σ k.succAbove)
  have key : ∀ (k : Fin 2) (σ : Fin 2 → ι),
      res (P := ab P.presheaf) (prodOpen_mono (inter_le_comp σ k.succAbove) le_rfl)
        (G (σ ∘ k.succAbove)) = tensorFam halgX halgY hP (fun σ : Fin 2 → ι => inter U σ)
          (fun _ : Unit => W) ((r k).rTensor _ t) σ () := by
    intro k σ
    rw [tensorFam_rTensor_resPi, hG]
    rfl
  have e : (fun σ : Fin 2 → ι =>
      res (P := ab P.presheaf) (prodOpen_mono (inter_le_comp σ (Fin.succAbove 0)) le_rfl)
          (G (σ ∘ Fin.succAbove 0)) -
        res (P := ab P.presheaf) (prodOpen_mono (inter_le_comp σ (Fin.succAbove 1)) le_rfl)
          (G (σ ∘ Fin.succAbove 1))) = fun σ => tensorFam halgX halgY hP
        (fun σ : Fin 2 → ι => inter U σ) (fun _ : Unit => W) ((r 0 - r 1).rTensor _ t) σ () := by
    funext σ
    rw [key 0 σ, key 1 σ, LinearMap.rTensor_sub, LinearMap.sub_apply, map_sub]
    rfl
  have hr : l ∘ₗ (r 0 - r 1) = 0 := by
    refine LinearMap.ext fun x => ?_
    have hx : (r 0 - r 1) x = d (ab X.presheaf) U 0 x := by
      funext σ
      rw [LinearMap.sub_apply, Pi.sub_apply, d_apply, Fin.sum_univ_two]
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
        ← sub_eq_add_neg]
      rfl
    rw [LinearMap.comp_apply, hx, hl, LinearMap.zero_apply]
  rw [e, slant_tensorFam, ← LinearMap.comp_apply, LinearMap.map_comp_rTensor, hr,
    TensorProduct.map_zero_left, LinearMap.zero_apply, map_zero]

end Slant

section Detection

open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ πX πY)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)
  {ι : Type w} [Finite ι] {κ : Type w'} (U : ι → X.Opens) (V : κ → Y.Opens)
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (hV : ∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ))
  (l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R)

omit [Finite ι] in
lemma le_inter_prodCover {m q r : ℕ} (σ : Fin q → ι) (b : Fin r → κ) (ε : Fin m → Fin q)
    (β : Fin m → Fin r) :
    prodOpen p₁ p₂ (inter U σ) (inter V b) ≤
      inter (prodCover p₁ p₂ U V) (fun j => (σ (ε j), b (β j))) :=
  le_iInf fun j => prodOpen_mono (inter_le_apply σ (ε j)) (inter_le_apply b (β j))

/-- The slant product of the values of a cochain `e` on the product cover at the indices
`(σ (ε j), b (β j))`. -/
noncomputable def ev {m r : ℕ} (e : C (ab P.presheaf) (prodCover p₁ p₂ U V) m)
    (b : Fin (r + 1) → κ) (ε : Fin (m + 1) → Fin 2) (β : Fin (m + 1) → Fin (r + 1)) :
    Γ(Y, inter V b) :=
  slant hP halgX halgY U hU l (inter V b) (hV r b) fun σ =>
    res (P := ab P.presheaf) (le_inter_prodCover U V σ b ε β) (e fun j => (σ (ε j), b (β j)))

lemma ev_d {m r : ℕ} (e : C (ab P.presheaf) (prodCover p₁ p₂ U V) m) (b : Fin (r + 1) → κ)
    (ε : Fin (m + 2) → Fin 2) (β : Fin (m + 2) → Fin (r + 1)) :
    ev hP halgX halgY U V hU hV l (d (ab P.presheaf) _ m e) b ε β =
      ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) •
        ev hP halgX halgY U V hU hV l e b (ε ∘ k.succAbove) (β ∘ k.succAbove) := by
  have h : (fun σ => res (P := ab P.presheaf) (le_inter_prodCover U V σ b ε β)
      (d (ab P.presheaf) _ m e fun j => (σ (ε j), b (β j)))) =
      ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) • fun σ => res (P := ab P.presheaf)
        (le_inter_prodCover U V σ b (ε ∘ k.succAbove) (β ∘ k.succAbove))
        (e fun j => (σ ((ε ∘ k.succAbove) j), b ((β ∘ k.succAbove) j))) := by
    funext σ
    rw [d_apply, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, res_res, Pi.smul_apply]
    rfl
  rw [ev, h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul]
  rfl

lemma ev_res {m r r' : ℕ} (e : C (ab P.presheaf) (prodCover p₁ p₂ U V) m)
    (b : Fin (r + 1) → κ) (θ : Fin (r' + 1) → Fin (r + 1)) (ε : Fin (m + 1) → Fin 2)
    (β : Fin (m + 1) → Fin (r' + 1)) :
    res (P := ab Y.presheaf) (inter_le_comp b θ)
        (ev hP halgX halgY U V hU hV l e (b ∘ θ) ε β) =
      ev hP halgX halgY U V hU hV l e b ε (θ ∘ β) := by
  rw [ev, ev, slant_res hP halgX halgY U hU l (inter_le_comp b θ) (hV r' (b ∘ θ)) (hV r b)]
  congr 1
  funext σ
  rw [res_res]
  rfl

/-- The chain-level Künneth operator `L`, the alternating sum of the slant products of `e`
along the shuffle paths `(σ 0, b 0), …, (σ 0, b s), (σ 1, b s), …, (σ 1, b m)`. -/
noncomputable def L (m : ℕ) (e : C (ab P.presheaf) (prodCover p₁ p₂ U V) (m + 1)) :
    C (ab Y.presheaf) V m := fun b =>
  ∑ s : Fin (m + 1), (-1 : ℤ) ^ (s : ℕ) •
    ev hP halgX halgY U V hU hV l e b (step ((s : ℕ) + 1)) (degen (s : ℕ))

lemma L_apply (m : ℕ) (e : C (ab P.presheaf) (prodCover p₁ p₂ U V) (m + 1))
    (b : Fin (m + 1) → κ) :
    L hP halgX halgY U V hU hV l m e b = ∑ s : Fin (m + 1), (-1 : ℤ) ^ (s : ℕ) •
      ev hP halgX halgY U V hU hV l e b (step ((s : ℕ) + 1)) (degen (s : ℕ)) :=
  rfl

/-- `L` anticommutes with the Čech differentials. -/
lemma L_d (hl : ∀ y : C (ab X.presheaf) U 0, l (d (ab X.presheaf) U 0 y) = 0) (n : ℕ)
    (c : C (ab P.presheaf) (prodCover p₁ p₂ U V) (n + 1)) :
    L hP halgX halgY U V hU hV l (n + 1) (d (ab P.presheaf) _ (n + 1) c) =
      -d (ab Y.presheaf) V n (L hP halgX halgY U V hU hV l n c) := by
  funext b
  have lhs : L hP halgX halgY U V hU hV l (n + 1) (d (ab P.presheaf) _ (n + 1) c) b =
      ∑ s ∈ Finset.range (n + 1 + 1), ∑ k ∈ Finset.range (n + 1 + 2), (-1 : ℤ) ^ (s + k) •
        ev hP halgX halgY U V hU hV l c b (step (s + 1) ∘ skip k) (degen s ∘ skip k) := by
    rw [L_apply, Finset.sum_range]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ev_d, Finset.sum_range, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, ← pow_add, succAbove_eq_skip]
  have rhs : d (ab Y.presheaf) V n (L hP halgX halgY U V hU hV l n c) b =
      ∑ t ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℤ) ^ (t + j) •
        ev hP halgX halgY U V hU hV l c b (step (t + 1)) (skip j ∘ degen t) := by
    rw [d_apply, Finset.sum_comm, Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [L_apply, map_sum, Finset.sum_range, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_zsmul, ev_res, smul_smul, ← pow_add, add_comm (j : ℕ), succAbove_eq_skip]
  have h₁ : ∀ s k, k < s → s ≤ n + 1 →
      ev hP halgX halgY U V hU hV l c b (step (s + 1) ∘ skip k) (degen s ∘ skip k) =
        ev hP halgX halgY U V hU hV l c b (step (s - 1 + 1)) (skip k ∘ degen (s - 1)) := by
    intro s k hk hs
    rw [step_comp_skip_of_le hk.le, degen_comp_skip_of_lt hk hs, Nat.sub_add_cancel (by omega)]
  have h₂ : ∀ s, s ≤ n + 1 →
      ev hP halgX halgY U V hU hV l c b (step (s + 1) ∘ skip s) (degen s ∘ skip s) =
        ev hP halgX halgY U V hU hV l c b (step s) id := by
    intro s _
    rw [step_comp_skip_of_le le_rfl, degen_comp_skip_self]
  have h₃ : ∀ s, s ≤ n + 1 →
      ev hP halgX halgY U V hU hV l c b (step (s + 1) ∘ skip (s + 1)) (degen s ∘ skip (s + 1)) =
        ev hP halgX halgY U V hU hV l c b (step (s + 1)) id := by
    intro s _
    rw [step_comp_skip_succ, degen_comp_skip_succ]
  have h₄ : ∀ s k, s + 1 < k → k ≤ n + 1 + 1 →
      ev hP halgX halgY U V hU hV l c b (step (s + 1) ∘ skip k) (degen s ∘ skip k) =
        ev hP halgX halgY U V hU hV l c b (step (s + 1)) (skip (k - 1) ∘ degen s) := by
    intro s k hk hk'
    rw [step_comp_skip_of_lt hk, degen_comp_skip_of_gt hk hk']
  have e₀ : (step 0 : Fin (n + 2) → Fin 2) = fun _ => 1 := by
    funext j
    apply Fin.ext
    rw [val_step]
    simp
  have e₁ : (step (n + 1 + 1) : Fin (n + 2) → Fin 2) = fun _ => 0 := by
    funext j
    apply Fin.ext
    rw [val_step]
    simp [j.isLt]
  have hQ : ev hP halgX halgY U V hU hV l c b (step 0) id -
      ev hP halgX halgY U V hU hV l c b (step (n + 1 + 1)) id = 0 := by
    rw [e₀, e₁, ev, ev, ← map_sub]
    refine Eq.trans ?_ (slant_coboundary hP halgX halgY U hU l hl (inter V b) (hV (n + 1) b)
      fun τ => res (P := ab P.presheaf) (le_inter_prodCover U V τ b (fun _ => 0) id)
        (c fun j => (τ 0, b j)))
    congr 1
    funext σ
    rw [Pi.sub_apply, res_res, res_res]
    rfl
  rw [Pi.neg_apply, lhs, rhs, shuffle_sum
    (fun s k => ev hP halgX halgY U V hU hV l c b (step (s + 1) ∘ skip k) (degen s ∘ skip k))
    (fun t j => ev hP halgX halgY U V hU hV l c b (step (t + 1)) (skip j ∘ degen t))
    (fun s => ev hP halgX halgY U V hU hV l c b (step s) id) (n + 1) h₁ h₂ h₃ h₄, hQ, zero_sub]

omit [Finite ι] in
/-- A face of `p₁^* z + p₂^* y`, restricted to `O`, with the index tuples of the two summands
given by `f₁` and `f₂`. -/
lemma res_face_pull_add (z : C (ab X.presheaf) U 1) (y : C (ab Y.presheaf) V 1) {m : ℕ}
    {τ : Fin m → ι × κ} {θ : Fin 2 → Fin m} {O : P.Opens} {h : O ≤ inter (prodCover p₁ p₂ U V) τ}
    (f₁ : Fin 2 → ι) (f₂ : Fin 2 → κ) (h₁ : Prod.fst ∘ (τ ∘ θ) = f₁)
    (h₂ : Prod.snd ∘ (τ ∘ θ) = f₂) (e₁ : O ≤ p₁ ⁻¹ᵁ inter U f₁) (e₂ : O ≤ p₂ ⁻¹ᵁ inter V f₂) :
    res (P := ab P.presheaf) h
      (face (pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 z +
        pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 y) τ θ) =
      (p₁.appLE (inter U f₁) O e₁).hom (z f₁) + (p₂.appLE (inter V f₂) O e₂).hom (y f₂) := by
  subst h₁ h₂
  rw [face, res_res, Pi.add_apply, map_add, pull_apply, pull_apply, res_appLE, res_appLE]

omit [Finite ι] in
lemma appLE_cocycle_const {Z : Scheme.{u}} {f : P ⟶ Z} {μ : Type*} {T : μ → Z.Opens}
    {x : C (ab Z.presheaf) T 1} (hx : d (ab Z.presheaf) T 1 x = 0) {ρ : Fin 2 → μ} (i : μ)
    (hρ : ρ = fun _ => i) {O : P.Opens} (e : O ≤ f ⁻¹ᵁ inter T ρ) :
    (f.appLE (inter T ρ) O e).hom (x ρ) = 0 := by
  subst hρ
  rw [cocycle_apply_const hx, map_zero]

omit [Finite ι] in
/-- The value of the product of the cocycles `p₁^* z k + p₂^* y k` on the shuffle path through
`σ` and `b` turning at `s`, restricted to `p₁⁻¹ (inter U σ) ⊓ p₂⁻¹ (inter V b)`. -/
lemma res_prod_path {n : ℕ} (z : Fin (n + 2) → C (ab X.presheaf) U 1)
    (y : Fin (n + 2) → C (ab Y.presheaf) V 1) (hz : ∀ k, d (ab X.presheaf) U 1 (z k) = 0)
    (hy : ∀ k, d (ab Y.presheaf) V 1 (y k) = 0) (s : Fin (n + 2)) (σ : Fin 2 → ι)
    (b : Fin (n + 2) → κ) :
    res (P := ab P.presheaf) (le_inter_prodCover U V σ b (step ((s : ℕ) + 1)) (degen (s : ℕ)))
      (prod P.presheaf (prodCover p₁ p₂ U V) (n + 2)
        (fun k => pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 (z k) +
          pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 (y k))
        (fun j => (σ (step ((s : ℕ) + 1) j), b (degen (s : ℕ) j)))) =
      (p₁.appLE (inter U σ) (prodOpen p₁ p₂ (inter U σ) (inter V b)) inf_le_left).hom (z s σ) *
        (p₂.appLE (inter V b) (prodOpen p₁ p₂ (inter U σ) (inter V b)) inf_le_right).hom
          (prod Y.presheaf V (n + 1) (y ∘ s.succAbove) b) := by
  rw [prod_apply, res_prod, Fin.prod_univ_succAbove _ s, prod_apply, map_prod]
  congr 1
  · refine (res_face_pull_add U V (z s) (y s) σ (fun _ => b s) ?_ ?_ inf_le_left
      (inf_le_right.trans (p₂.preimage_mono (inter_le_comp b fun _ => s)))).trans ?_
    · funext a
      exact congrArg σ (congrFun (step_comp_edge_self s) a)
    · funext a
      exact congrArg b (congrFun (degen_comp_edge_self s) a)
    · rw [appLE_cocycle_const (hy s) (b s) rfl, add_zero]
  · refine Finset.prod_congr rfl fun k _ => ?_
    refine (res_face_pull_add U V (z (s.succAbove k)) (y (s.succAbove k))
      (fun _ => σ (step ((s : ℕ) + 1) (edge (s.succAbove k) 0))) (b ∘ edge k) ?_ ?_
      (inf_le_left.trans (p₁.preimage_mono (inter_le_comp σ fun _ =>
        step ((s : ℕ) + 1) (edge (s.succAbove k) 0))))
      (inf_le_right.trans (p₂.preimage_mono (inter_le_comp b (edge k))))).trans ?_
    · funext a
      exact congrArg σ (congrFun (step_comp_edge_succAbove s k) a)
    · funext a
      exact congrArg b (congrFun (degen_comp_edge_succAbove s k) a)
    · rw [appLE_cocycle_const (hz _) _ rfl, zero_add, face, appLE_res]
      rfl

/-- `L` sends the product of the cocycles `p₁^* z k + p₂^* y k` to the product of
`y 1, …, y (n + 1)`. -/
lemma L_prod (n : ℕ) (z : Fin (n + 2) → C (ab X.presheaf) U 1)
    (y : Fin (n + 2) → C (ab Y.presheaf) V 1) (hz : ∀ k, d (ab X.presheaf) U 1 (z k) = 0)
    (hy : ∀ k, d (ab Y.presheaf) V 1 (y k) = 0) (hz₀ : l (z 0) = 1)
    (hzr : ∀ r : Fin (n + 1), l (z r.succ) = 0) :
    L hP halgX halgY U V hU hV l (n + 1) (prod P.presheaf (prodCover p₁ p₂ U V) (n + 2)
        (fun k => pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 (z k) +
          pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 (y k))) =
      prod Y.presheaf V (n + 1) (Fin.tail y) := by
  funext b
  have hev : ∀ s : Fin (n + 2), ev hP halgX halgY U V hU hV l
      (prod P.presheaf (prodCover p₁ p₂ U V) (n + 2)
        (fun k => pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 (z k) +
          pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 (y k)))
      b (step ((s : ℕ) + 1)) (degen (s : ℕ)) =
        HSMul.hSMul (α := R) (β := Γ(Y, inter V b)) (l (z s))
          (prod Y.presheaf V (n + 1) (y ∘ s.succAbove) b) := fun s =>
    (DFunLike.congr_arg _ (funext fun σ => res_prod_path U V z y hz hy s σ b)).trans
      (slant_mul hP halgX halgY U hU l (inter V b) (hV (n + 1) b) (z s) _)
  rw [L_apply, Fin.sum_univ_succ]
  simp only [hev]
  simp only [Fin.val_zero, pow_zero, one_smul, hz₀, hzr, zero_smul, smul_zero,
    Finset.sum_const_zero, add_zero, Fin.succAbove_zero]
  rfl

end Detection

end KunnethDetection

open KunnethDetection in
/-- **Künneth detection.** If the product of the degree-one cocycles `p₁^* z k + p₂^* y k`
(`k = 0, …, n + 1`) is a coboundary on the product cover, then so is the product of
`y 1, …, y (n + 1)`: apply the chain map `-L`, which anticommutes with `d` and sends the product
to the product of the `y`'s. -/
theorem kunnethDetection : KunnethDetectionStatement.{w, w', u} := by
  intro R X Y P πX πY p₁ p₂ hP _ halgX _ halgY ι κ _ _ U V hU hV l hl n z y hz hy hz₀ hzr c hc
  refine ⟨-L hP halgX halgY U V hU hV l n c, ?_⟩
  rw [map_neg, ← L_d hP halgX halgY U V hU hV l hl n c, ← hc,
    L_prod hP halgX halgY U V hU hV l n z y hz hy hz₀ hzr]

end Langlands.Cohomology.Cech
