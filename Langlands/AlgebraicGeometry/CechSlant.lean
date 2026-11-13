import Langlands.AlgebraicGeometry.CechKunneth

/-! # Linear slant maps on all-sequence Čech cochains -/

noncomputable section

universe w w' u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

namespace Langlands.Cohomology.Cech.KunnethDetection

open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

section Scalars

variable {R : CommRingCat.{u}} {X P : Scheme.{u}}
  {πX : X ⟶ Spec R} {πP : P ⟶ Spec R} {f : P ⟶ X}
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : P.Opens, Algebra R Γ(P, W)]
  (halgP : ∀ W : P.Opens, algebraMap R Γ(P, W) = (secHom πP W).hom)
  (hπ : f ≫ πX = πP)

/-- Pullback of sections for a morphism over `Spec R` preserves the `R`-algebra structures. -/
def appLEAlgHom (U : X.Opens) (W : P.Opens) (hW : W ≤ f ⁻¹ᵁ U) :
    Γ(X, U) →ₐ[R] Γ(P, W) :=
  { (f.appLE U W hW).hom with
    commutes' := fun r => by
      change (f.appLE U W hW).hom (algebraMap R Γ(X, U) r) =
        algebraMap R Γ(P, W) r
      rw [halgX, halgP, ← CommRingCat.comp_apply]
      have h := Scheme.Hom.appLE_comp_appLE f πX ⊤ U W
        (le_top.trans_eq πX.preimage_top.symm) hW
      change ((Scheme.ΓSpecIso R).inv ≫ πX.appLE ⊤ U
        (le_top.trans_eq πX.preimage_top.symm) ≫ f.appLE U W hW).hom r = _
      rw [h, ← hπ]
      rfl }

include halgX halgP hπ in
lemma appLE_smul (U : X.Opens) (W : P.Opens) (hW : W ≤ f ⁻¹ᵁ U)
    (r : R) (a : Γ(X, U)) :
    (f.appLE U W hW).hom (r • a) = r • (f.appLE U W hW).hom a :=
  (appLEAlgHom halgX halgP hπ U W hW).toLinearMap.map_smul r a

end Scalars

section LinearSlant

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}}
  {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R} {πP : P ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ πX πY)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)
  [∀ W : P.Opens, Algebra R Γ(P, W)]
  (halgP : ∀ W : P.Opens, algebraMap R Γ(P, W) = (secHom πP W).hom)
  (hπ : p₁ ≫ πX = πP)

include halgP hπ in
lemma tensorFam_smul {α β : Type*} (U : α → X.Opens) (V : β → Y.Opens)
    (r : R) (t : (∀ a, Γ(X, U a)) ⊗[R] (∀ b, Γ(Y, V b))) :
    tensorFam halgX halgY hP U V (r • t) = r • tensorFam halgX halgY hP U V t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.smul_tmul']
    funext a b
    simp only [tensorFam_tmul, Pi.smul_apply]
    change (p₁.appLE (U a) _ inf_le_left).hom (r • x a) *
        (p₂.appLE (V b) _ inf_le_right).hom (y b) =
      r • ((p₁.appLE (U a) _ inf_le_left).hom (x a) *
        (p₂.appLE (V b) _ inf_le_right).hom (y b))
    rw [appLE_smul halgX halgP hπ, smul_mul_assoc]
  | add x y hx hy =>
    rw [smul_add, map_add, hx, hy, map_add, smul_add]

variable {ι : Type w} [Finite ι] (U : ι → X.Opens)
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R)

include halgP hπ in
lemma slant_smul (W : Y.Opens) (hW : IsAffineOpen W) (r : R)
    (F : ∀ σ : Fin 2 → ι, Γ(P, prodOpen p₁ p₂ (inter U σ) W)) :
    slant hP halgX halgY U hU l W hW (r • F) =
      r • slant hP halgX halgY U hU l W hW F := by
  have he : ∀ t, (tensorEquiv hP halgX halgY U hU W hW) (r • t) =
      r • (tensorEquiv hP halgX halgY U hU W hW) t :=
    tensorFam_smul hP halgX halgY halgP hπ _ _ r
  have hinv :
      (tensorEquiv hP halgX halgY U hU W hW).symm
          (r • (fun σ (_ : Unit) => F σ)) =
        r • (tensorEquiv hP halgX halgY U hU W hW).symm (fun σ (_ : Unit) => F σ) := by
    apply (tensorEquiv hP halgX halgY U hU W hW).injective
    rw [AddEquiv.apply_symm_apply, he, AddEquiv.apply_symm_apply]
  change TensorProduct.lid R Γ(Y, W) (TensorProduct.map l (LinearMap.proj ())
      ((tensorEquiv hP halgX halgY U hU W hW).symm
        (r • (fun σ (_ : Unit) => F σ)))) = _
  rw [hinv, map_smul, map_smul]
  rfl

variable {κ : Type w'} (V : κ → Y.Opens)
  (hV : ∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ))

include halgP hπ in
lemma ev_smul {m n : ℕ}
    (e : ∀ σ : Fin (m + 1) → ι × κ, Γ(P, inter (prodCover p₁ p₂ U V) σ))
    (b : Fin (n + 1) → κ) (ε : Fin (m + 1) → Fin 2)
    (β : Fin (m + 1) → Fin (n + 1)) (r : R) :
    ev hP halgX halgY U V hU hV l (r • e) b ε β =
      r • ev hP halgX halgY U V hU hV l e b ε β := by
  unfold ev
  rw [← slant_smul hP halgX halgY halgP hπ]
  congr 1
  funext σ
  exact (resAlgHom πP halgP (le_inter_prodCover U V σ b ε β)).toLinearMap.map_smul r _

omit [∀ W : P.Opens, Algebra R Γ(P, W)] in
lemma ev_add {m n : ℕ} (e e' : C (ab P.presheaf) (prodCover p₁ p₂ U V) m)
    (b : Fin (n + 1) → κ) (ε : Fin (m + 1) → Fin 2)
    (β : Fin (m + 1) → Fin (n + 1)) :
    ev hP halgX halgY U V hU hV l (e + e') b ε β =
      ev hP halgX halgY U V hU hV l e b ε β +
        ev hP halgX halgY U V hU hV l e' b ε β := by
  unfold ev
  simp only [Pi.add_apply, map_add]
  exact map_add (slant hP halgX halgY U hU l (inter V b) (hV n b)) _ _

/-- The shuffle slant operator as an `R`-linear map. -/
def LLinearMap (n : ℕ) :
    (∀ σ : Fin (n + 2) → ι × κ, Γ(P, inter (prodCover p₁ p₂ U V) σ)) →ₗ[R]
      ∀ b : Fin (n + 1) → κ, Γ(Y, inter V b) where
  toFun := L hP halgX halgY U V hU hV l n
  map_add' e e' := by
    funext b
    simp only [L_apply, ev_add, smul_add, Finset.sum_add_distrib, Pi.add_apply]
  map_smul' r e := by
    funext b
    simp only [L_apply, ev_smul hP halgX halgY halgP hπ, Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum (M := R) (N := Γ(Y, inter V b))]
    exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _

end LinearSlant

section Bottom

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

/-- The degree-one slant operator kills degree-one coboundaries. -/
lemma L_zero_d
    (hl : ∀ y : C (ab X.presheaf) U 0, l (d (ab X.presheaf) U 0 y) = 0)
    (c : C (ab P.presheaf) (prodCover p₁ p₂ U V) 0) :
    L hP halgX halgY U V hU hV l 0 (d (ab P.presheaf) _ 0 c) = 0 := by
  funext b
  rw [L_apply, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul]
  rw [ev_d, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  have e₀ : (step (0 + 1) ∘ (Fin.succAbove 0 : Fin 1 → Fin 2)) = fun _ => (1 : Fin 2) := by
    funext j
    fin_cases j
    rfl
  have e₁ : (step (0 + 1) ∘ (Fin.succAbove 1 : Fin 1 → Fin 2)) = fun _ => (0 : Fin 2) := by
    funext j
    fin_cases j
    rfl
  have b₀ : (degen 0 ∘ (Fin.succAbove 0 : Fin 1 → Fin 2)) = id := by
    funext j
    fin_cases j
    rfl
  have b₁ : (degen 0 ∘ (Fin.succAbove 1 : Fin 1 → Fin 2)) = id := by
    funext j
    fin_cases j
    rfl
  rw [e₀, e₁, b₀, b₁]
  unfold ev
  rw [← sub_eq_add_neg, ← map_sub]
  refine Eq.trans ?_ (slant_coboundary hP halgX halgY U hU l hl (inter V b) (hV 0 b)
    (fun τ => res (P := ab P.presheaf)
      (le_inter_prodCover U V τ b (fun _ => 0) id) (c fun j => (τ 0, b j))))
  congr 1
  funext σ
  rw [Pi.sub_apply, res_res, res_res]
  rfl

end Bottom

end Langlands.Cohomology.Cech.KunnethDetection
