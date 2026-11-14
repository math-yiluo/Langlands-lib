import Langlands.AlgebraicGeometry.CechSlant

/-! # Right-axis cup and shuffle slant -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe w w' u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

namespace Langlands.Cohomology.Cech.KunnethDetection

open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}}
  {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ πX πY)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)
  {ι : Type w} [Finite ι] (U : ι → X.Opens)
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R)

lemma slant_tensorFam_mul_right (W : Y.Opens) (hW : IsAffineOpen W)
    (t : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) ⊗[R] (∀ _ : Unit, Γ(Y, W)))
    (y : Γ(Y, W)) :
    slant hP halgX halgY U hU l W hW (fun σ =>
        (p₂.appLE W (prodOpen p₁ p₂ (inter U σ) W) inf_le_right).hom y *
          tensorFam halgX halgY hP (fun σ : Fin 2 → ι => inter U σ)
            (fun _ : Unit => W) t σ ()) =
      y * TensorProduct.lid R Γ(Y, W) (TensorProduct.map l (LinearMap.proj ()) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x z =>
    simp only [tensorFam_tmul, TensorProduct.map_tmul, TensorProduct.lid_tmul,
      LinearMap.proj_apply]
    have hf : (fun σ =>
        (p₂.appLE W (prodOpen p₁ p₂ (inter U σ) W) inf_le_right).hom y *
          ((p₁.appLE (inter U σ) (prodOpen p₁ p₂ (inter U σ) W) inf_le_left).hom (x σ) *
            (p₂.appLE W (prodOpen p₁ p₂ (inter U σ) W) inf_le_right).hom (z ()))) =
        (fun σ =>
          (p₁.appLE (inter U σ) (prodOpen p₁ p₂ (inter U σ) W) inf_le_left).hom (x σ) *
            (p₂.appLE W (prodOpen p₁ p₂ (inter U σ) W) inf_le_right).hom (y * z ())) := by
      funext σ
      rw [map_mul]
      ring
    rw [hf, slant_mul]
    exact (mul_smul_comm (l x) y (z ())).symm
  | add t t' ht ht' =>
    simp only [map_add, Pi.add_apply, mul_add]
    change slant hP halgX halgY U hU l W hW
      ((fun σ => (p₂.appLE W (prodOpen p₁ p₂ (inter U σ) W) inf_le_right).hom y *
        tensorFam halgX halgY hP (fun σ : Fin 2 → ι => inter U σ)
          (fun _ : Unit => W) t σ ()) +
       (fun σ => (p₂.appLE W (prodOpen p₁ p₂ (inter U σ) W) inf_le_right).hom y *
        tensorFam halgX halgY hP (fun σ : Fin 2 → ι => inter U σ)
          (fun _ : Unit => W) t' σ ())) = _
    rw [map_add, ht, ht']

/-- Slant is linear over sections of the second factor. -/
lemma slant_mul_pull_right (W : Y.Opens) (hW : IsAffineOpen W)
    (F : ∀ σ : Fin 2 → ι, Γ(P, prodOpen p₁ p₂ (inter U σ) W)) (y : Γ(Y, W)) :
    slant hP halgX halgY U hU l W hW (fun σ =>
        (p₂.appLE W (prodOpen p₁ p₂ (inter U σ) W) inf_le_right).hom y * F σ) =
      y * slant hP halgX halgY U hU l W hW F := by
  obtain ⟨t, ht⟩ := (tensorEquiv hP halgX halgY U hU W hW).surjective fun σ _ => F σ
  have hF : F = fun σ => tensorFam halgX halgY hP (fun σ : Fin 2 → ι => inter U σ)
      (fun _ : Unit => W) t σ () := funext fun σ => (congrFun (congrFun ht σ) ()).symm
  rw [hF, slant_tensorFam, slant_tensorFam_mul_right]

lemma degen_zero_comp_edge_zero {n : ℕ} :
    (degen 0 : Fin (n + 3) → Fin (n + 2)) ∘ edge (0 : Fin (n + 2)) =
      fun _ => (0 : Fin (n + 2)) := by
  refine fin_two_funext (Fin.ext ?_) (Fin.ext ?_)
  all_goals
    simp only [Function.comp_apply, edge_zero, edge_one, val_degen,
      Fin.val_castSucc, Fin.val_succ, Fin.val_zero]
    split_ifs <;> omega

lemma step_succ_comp_succ {n : ℕ} (s : ℕ) :
    (step (s + 2) : Fin (n + 3) → Fin 2) ∘ Fin.succ =
      (step (s + 1) : Fin (n + 2) → Fin 2) := by
  funext j
  apply Fin.ext
  simp only [Function.comp_apply, val_step, Fin.val_succ]
  split_ifs <;> omega

lemma degen_succ_comp_succ {n : ℕ} (s : Fin (n + 1)) :
    (degen ((s : ℕ) + 1) : Fin (n + 3) → Fin (n + 2)) ∘ Fin.succ =
      Fin.succ ∘ (degen (s : ℕ) : Fin (n + 2) → Fin (n + 1)) := by
  funext j
  apply Fin.ext
  have := s.isLt
  have := j.isLt
  simp only [Function.comp_apply, val_degen, Fin.val_succ]
  split_ifs <;> omega

lemma degen_succ_comp_edge_zero {n : ℕ} (s : Fin (n + 1)) :
    (degen ((s : ℕ) + 1) : Fin (n + 3) → Fin (n + 2)) ∘ edge (0 : Fin (n + 2)) =
      edge (0 : Fin (n + 1)) := by
  refine fin_two_funext (Fin.ext ?_) (Fin.ext ?_)
  all_goals
    simp only [Function.comp_apply, edge_zero, edge_one, val_degen,
      Fin.val_castSucc, Fin.val_succ, Fin.val_zero]
    split_ifs <;> omega

variable {κ : Type w'} (V : κ → Y.Opens)
  (hV : ∀ (n : ℕ) (b : Fin (n + 1) → κ), IsAffineOpen (inter V b))

/-- Evaluation extracts a right-axis cup factor before applying slant. -/
lemma ev_cup_pull_right {m n : ℕ} (y : C (ab Y.presheaf) V 1)
    (e : C (ab P.presheaf) (prodCover p₁ p₂ U V) m)
    (b : Fin (n + 1) → κ) (ε : Fin (m + 2) → Fin 2)
    (β : Fin (m + 2) → Fin (n + 1)) :
    ev hP halgX halgY U V hU hV l
        (cup₁ P.presheaf (prodCover p₁ p₂ U V)
          (pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 y) e)
        b ε β =
      HMul.hMul (α := Γ(Y, inter V b)) (β := Γ(Y, inter V b))
        (face y b (β ∘ edge 0))
        (ev hP halgX halgY U V hU hV l e b (ε ∘ Fin.succ) (β ∘ Fin.succ)) := by
  unfold ev
  rw [← slant_mul_pull_right]
  congr 1
  funext σ
  rw [cup₁_apply, res_mul, face_pull, res_appLE]
  congr 1
  · rw [face, face, appLE_res, appLE_res]
    rfl
  · rw [face, res_res]
    rfl

/-- Cup by a degree-one cochain pulled back from the right factor. -/
def rightAxisCup (y : C (ab Y.presheaf) V 1) (m : ℕ) :
    C (ab P.presheaf) (prodCover p₁ p₂ U V) m →+
      C (ab P.presheaf) (prodCover p₁ p₂ U V) (m + 1) where
  toFun e := cup₁ P.presheaf (prodCover p₁ p₂ U V)
    (pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 y) e
  map_zero' := by
    funext τ
    simp only [cup₁_apply, face, Pi.zero_apply, map_zero, mul_zero]
  map_add' e e' := by
    funext τ
    simp only [cup₁_apply, face_add, mul_add, Pi.add_apply]

/-- Right-axis creation anticommutes with shuffle slant on arbitrary cochains. -/
lemma L_cup_pull_right (n : ℕ) (y : C (ab Y.presheaf) V 1)
    (hy : d (ab Y.presheaf) V 1 y = 0)
    (e : C (ab P.presheaf) (prodCover p₁ p₂ U V) (n + 1)) :
    L hP halgX halgY U V hU hV l (n + 1) (rightAxisCup U V y (n + 1) e) =
      -cup₁ Y.presheaf V y (L hP halgX halgY U V hU hV l n e) := by
  change L hP halgX halgY U V hU hV l (n + 1)
    (cup₁ P.presheaf (prodCover p₁ p₂ U V)
      (pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 y) e) = _
  funext b
  rw [L_apply, Fin.sum_univ_succ]
  have hzero : ev hP halgX halgY U V hU hV l
      (cup₁ P.presheaf (prodCover p₁ p₂ U V)
        (pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 y) e)
      b (step (0 + 1)) (degen 0) = 0 := by
    rw [ev_cup_pull_right, degen_zero_comp_edge_zero, face]
    simp only [Function.comp_def]
    rw [cocycle_apply_const hy, map_zero, zero_mul]
  simp only [Fin.val_zero, pow_zero, one_smul, hzero, zero_add, Pi.neg_apply, cup₁_apply]
  have hs : ∀ s : Fin (n + 1),
      ev hP halgX halgY U V hU hV l
          (cup₁ P.presheaf (prodCover p₁ p₂ U V)
            (pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 y) e)
          b (step ((s : ℕ) + 1 + 1)) (degen ((s : ℕ) + 1)) =
        HMul.hMul (α := Γ(Y, inter V b)) (β := Γ(Y, inter V b))
          (face y b (edge 0))
          (res (P := ab Y.presheaf) (inter_le_comp b Fin.succ)
            (ev hP halgX halgY U V hU hV l e (b ∘ Fin.succ)
              (step ((s : ℕ) + 1)) (degen (s : ℕ)))) := by
    intro s
    rw [ev_cup_pull_right, degen_succ_comp_edge_zero,
      step_succ_comp_succ, degen_succ_comp_succ, ← ev_res]
  simp only [hs, Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
  rw [Finset.sum_neg_distrib]
  congr 1
  simp only [face]
  rw [L_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_zsmul, mul_smul_comm]

end Langlands.Cohomology.Cech.KunnethDetection
