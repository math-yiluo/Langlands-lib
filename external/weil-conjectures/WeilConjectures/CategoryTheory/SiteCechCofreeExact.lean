/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SiteCechComplex
public import WeilConjectures.CategoryTheory.Sites.CechComplex

/-!
# Exactness of the chosen Čech complex of a cofree presheaf

Source: Stacks Project, Cohomology on Sites, Tag 03AT, and the cofree-presheaf
contraction in `WeilConjectures.CategoryTheory.Sites.CechComplex`.
(blueprint: lem-weil-pbc-site-cech-cofree-exact)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SiteCechComplex

variable {C : Type u} [Category.{v} C] {T : Type (max u v)} {U : C}
  {f : T → C} {hom : ∀ t, f t ⟶ U} (S : SiteCechComplex f hom)

private theorem cofree_face_eq (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) {k m : ℕ}
    (c : S.cochains (Presheaf.cofree P) k) (t : Fin (m + 1) → T)
    (α : Fin (k + 1) → Fin (m + 1)) {t' : Fin (k + 1) → T} (h : t ∘ α = t')
    (Z : C) (g : Z ⟶ S.W m t) (g' : Z ⟶ S.W k t')
    (hpr : ∀ l, HEq (g ≫ S.pr m t (α l)) (g' ≫ S.pr k t' l)) :
    c (t ∘ α) Z (g ≫ S.indexMap t α) = c t' Z g' := by
  subst t'
  congr 1
  obtain ⟨_, _, hu⟩ := S.universal k (t ∘ α) Z (fun l ↦ g' ≫ S.pr k (t ∘ α) l)
    (by intro l; simp only [Category.assoc, S.comm])
  apply (hu _ ?_).trans (hu g' (fun _ ↦ rfl)).symm
  intro l
  rw [Category.assoc, S.indexMap_pr]
  exact eq_of_heq (hpr l)

private theorem cofree_d_apply (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (k : ℕ)
    (c : S.cochains (Presheaf.cofree P) k) (t : Fin (k + 2) → T)
    (Z : C) (g : Z ⟶ S.W (k + 1) t) :
    S.differentialValue (Presheaf.cofree P) k c t Z g =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ i.val •
        c (t ∘ i.succAbove) Z (g ≫ S.indexMap t i.succAbove) := by
  unfold differentialValue
  erw [Finset.sum_apply, Finset.sum_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The cofree presheaf has an exact positive-degree Čech complex.
Source: Stacks 03AT (insertion contraction), as implemented for categorical products
by `CategoryTheory.Presheaf.exactAt_cechComplex_cofree`.
(blueprint: lem-weil-pbc-site-cech-cofree-exact)

Proof: evaluate a cochain at an object Z and a map to a chosen fibre product.
Group these evaluations by their common composite Z -> U. For each composite admitting
lifts to the family, choose one lift once, and prepend it to every tuple. The universal
property supplies the map to the enlarged fibre product. Evaluate the cocycle equation
on this enlarged tuple: its zeroth face is the original cochain, and its other faces
are the negative of the differential of the cochain obtained by insertion. Thus the
latter is a primitive. A tuple always supplies a lift by its zeroth projection; if
there are no tuples there are no components to check. No covering or injectivity
hypothesis is involved. -/
theorem exactAt_cofree
    {C : Type u} [Category.{v} C] {T : Type (max u v)} {U : C}
    {f : T → C} {hom : ∀ t, f t ⟶ U} (S : SiteCechComplex f hom)
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (q : ℕ) :
    (S.complex (Presheaf.cofree P)).ExactAt (q + 1) := by
  classical
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro c hc
  change (S.complex (Presheaf.cofree P)).d (q + 1) ((q + 1) + 1) c = 0 at hc
  change ∃ b, (S.complex (Presheaf.cofree P)).d q (q + 1) b = c
  simp only [complex, CochainComplex.of_d] at hc ⊢
  change S.differentialValue (Presheaf.cofree P) (q + 1) c = 0 at hc
  change ∃ b, S.differentialValue (Presheaf.cofree P) q b = c
  let j (Z : C) (g : Z ⟶ U) (h : ∃ a, ∃ l : Z ⟶ f a, l ≫ hom a = g) := h.choose
  let lam (Z : C) (g : Z ⟶ U) (h : ∃ a, ∃ l : Z ⟶ f a, l ≫ hom a = g) :
      Z ⟶ f (j Z g h) := h.choose_spec.choose
  have hlam (Z g h) : lam Z g h ≫ hom (j Z g h) = g := h.choose_spec.choose_spec
  have hex {k : ℕ} (t : Fin (k + 1) → T) (Z : C) (g : Z ⟶ S.W k t) :
      ∃ a, ∃ l : Z ⟶ f a, l ≫ hom a = g ≫ S.pr k t 0 ≫ hom (t 0) :=
    ⟨t 0, g ≫ S.pr k t 0, by simp only [Category.assoc]⟩
  let lift {k : ℕ} (t : Fin (k + 1) → T) (Z : C) (g : Z ⟶ S.W k t)
      (v : Z ⟶ U) (hv : g ≫ S.pr k t 0 ≫ hom (t 0) = v)
      (h : ∃ a, ∃ l : Z ⟶ f a, l ≫ hom a = v) :
      Z ⟶ S.W (k + 1) (Fin.cons (j Z v h) t) :=
    (S.universal (k + 1) (Fin.cons (j Z v h) t) Z
      (Fin.cases (lam Z v h) (fun l ↦ g ≫ S.pr k t l)) (by
        intro l
        cases l using Fin.cases with
        | zero => rfl
        | succ l =>
          change (g ≫ S.pr k t l) ≫ hom (t l) = lam Z v h ≫ hom (j Z v h)
          rw [Category.assoc, S.comm, hv, hlam])).choose
  have hlift {k : ℕ} (t : Fin (k + 1) → T) (Z : C) (g : Z ⟶ S.W k t)
      (v : Z ⟶ U) (hv : g ≫ S.pr k t 0 ≫ hom (t 0) = v)
      (h : ∃ a, ∃ l : Z ⟶ f a, l ≫ hom a = v) (l : Fin (k + 2)) :
      lift t Z g v hv h ≫ S.pr (k + 1) (Fin.cons (j Z v h) t) l =
        Fin.cases (lam Z v h) (fun l ↦ g ≫ S.pr k t l) l :=
    (S.universal _ _ _ _ (by
      intro l
      cases l using Fin.cases with
      | zero => rfl
      | succ l =>
        change (g ≫ S.pr k t l) ≫ hom (t l) = lam Z v h ≫ hom (j Z v h)
        rw [Category.assoc, S.comm, hv, hlam])).choose_spec.1 l
  let b : S.cochains (Presheaf.cofree P) q := fun t Z g ↦
    c (Fin.cons (j Z _ (hex t Z g)) t) Z (lift t Z g _ rfl (hex t Z g))
  have hb (t : Fin (q + 1) → T) (Z : C) (g : Z ⟶ S.W q t) (v : Z ⟶ U)
      (hv : g ≫ S.pr q t 0 ≫ hom (t 0) = v)
      (h : ∃ a, ∃ l : Z ⟶ f a, l ≫ hom a = v) :
      b t Z g = c (Fin.cons (j Z v h) t) Z (lift t Z g v hv h) := by
    subst v
    rfl
  refine ⟨b, ?_⟩
  funext t Z g
  let v := g ≫ S.pr (q + 1) t 0 ≫ hom (t 0)
  have hex' := hex t Z g
  let J := j Z v hex'
  let G := lift t Z g v rfl hex'
  have h₀ := congrArg (fun c' ↦ c' (Fin.cons J t) Z G) hc
  rw [S.cofree_d_apply, Fin.sum_univ_succ] at h₀
  change _ = (0 : P.obj (op Z)) at h₀
  have e₀ : c ((Fin.cons J t : Fin (q + 3) → T) ∘ (0 : Fin (q + 3)).succAbove) Z
      (G ≫ S.indexMap (Fin.cons J t) (0 : Fin (q + 3)).succAbove) = c t Z g := by
    apply S.cofree_face_eq P c (Fin.cons J t) _ (by funext l; simp)
    intro l
    exact heq_of_eq (hlift t Z g v rfl hex' l.succ)
  have e (i : Fin (q + 2)) :
      c ((Fin.cons J t : Fin (q + 3) → T) ∘ i.succ.succAbove) Z
        (G ≫ S.indexMap (Fin.cons J t) i.succ.succAbove) =
      b (t ∘ i.succAbove) Z (g ≫ S.indexMap t i.succAbove) := by
    have hv : (g ≫ S.indexMap t i.succAbove) ≫
        S.pr q (t ∘ i.succAbove) 0 ≫ hom ((t ∘ i.succAbove) 0) = v := by
      rw [Category.assoc, ← Category.assoc (S.indexMap t i.succAbove), S.indexMap_pr]
      exact congrArg (fun a ↦ g ≫ a) (S.comm (q + 1) t (i.succAbove 0))
    rw [hb _ _ _ v hv hex']
    apply S.cofree_face_eq P c (Fin.cons J t) _
      (by funext l; cases l using Fin.cases with | zero => rfl | succ l => simp)
    intro l
    cases l using Fin.cases with
    | zero =>
      exact heq_of_eq ((hlift t Z g v rfl hex' 0).trans
        (hlift (t ∘ i.succAbove) Z (g ≫ S.indexMap t i.succAbove) v hv hex' 0).symm)
    | succ l =>
      rw [Fin.succ_succAbove_succ]
      apply heq_of_eq
      rw [hlift t Z g v rfl hex',
        hlift (t ∘ i.succAbove) Z (g ≫ S.indexMap t i.succAbove) v hv hex']
      simp only [Fin.cases_succ, Category.assoc, S.indexMap_pr]
  rw [e₀] at h₀
  simp only [e, Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib,
    Fin.val_zero, pow_zero, one_smul] at h₀
  rw [S.cofree_d_apply]
  exact (add_neg_eq_zero.mp h₀).symm

end CategoryTheory.SiteCechComplex
