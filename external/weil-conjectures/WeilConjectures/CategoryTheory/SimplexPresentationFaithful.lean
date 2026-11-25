/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.NormalForms
import Mathlib.AlgebraicTopology.SimplicialObject.II

/-! # Faithfulness of the simplex generators and relations presentation -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial SimplexCategoryGenRel
noncomputable section

private def dualQuiver : FreeSimplexQuiver ⥤q SimplexCategoryGenRelᵒᵖ where
  obj n := op (mk (n.len + 1))
  map f := match f with
    | .δ i => (σ i).op
    | .σ i => (δ i.succ.castSucc).op

private theorem dual_relations : ∀ (a b : Paths FreeSimplexQuiver) (f g : a ⟶ b),
    FreeSimplexQuiver.homRel f g → (Paths.lift dualQuiver).map f =
      (Paths.lift dualQuiver).map g := by
  intro a b f g h
  cases h with
  | δ_comp_δ h =>
    simp only [Functor.map_comp, Paths.of_map, Paths.lift_toPath]
    apply Quiver.Hom.unop_inj
    simpa [dualQuiver, unop_comp] using (σ_comp_σ h).symm
  | @δ_comp_σ_of_le n i j h =>
    simp only [Functor.map_comp, Paths.of_map, Paths.lift_toPath]
    apply Quiver.Hom.unop_inj
    have hij : i.castSucc < j.succ.castSucc := by
      simp only [Fin.lt_def, Fin.le_def, Fin.val_castSucc, Fin.val_succ] at h ⊢
      omega
    simpa [dualQuiver, unop_comp, Fin.castSucc_succ] using
      (δ_comp_σ_of_gt (i := j.succ.castSucc) (j := i) hij)
  | @δ_comp_σ_self n i =>
    simp only [Functor.map_comp, Paths.of_map, Paths.lift_toPath]
    apply Quiver.Hom.unop_inj
    change δ i.succ.castSucc ≫ σ i.castSucc = 𝟙 _
    simpa only [Fin.castSucc_succ] using (δ_comp_σ_succ (i := i.castSucc))
  | @δ_comp_σ_succ n i =>
    simp only [Functor.map_comp, Paths.of_map, Paths.lift_toPath]
    apply Quiver.Hom.unop_inj
    change δ i.succ.castSucc ≫ σ i.succ = 𝟙 _
    exact δ_comp_σ_self
  | @δ_comp_σ_of_gt n i j h =>
    simp only [Functor.map_comp, Paths.of_map, Paths.lift_toPath]
    apply Quiver.Hom.unop_inj
    have hij : j.succ.castSucc ≤ i.castSucc := by
      simp only [Fin.lt_def, Fin.le_def, Fin.val_castSucc, Fin.val_succ] at h ⊢
      omega
    simpa [dualQuiver, unop_comp, Fin.castSucc_succ] using
      (δ_comp_σ_of_le (i := j.succ.castSucc) (j := i) hij)
  | @σ_comp_σ n i j h =>
    simp only [Functor.map_comp, Paths.of_map, Paths.lift_toPath]
    apply Quiver.Hom.unop_inj
    have hij : i.succ.castSucc ≤ j.succ.castSucc := by simpa using h
    simpa [dualQuiver, unop_comp, Fin.castSucc_succ] using
      (δ_comp_δ (i := i.succ.castSucc) (j := j.succ.castSucc) hij).symm

private def dual : SimplexCategoryGenRel ⥤ SimplexCategoryGenRelᵒᵖ :=
  CategoryTheory.Quotient.lift FreeSimplexQuiver.homRel (Paths.lift dualQuiver) dual_relations

private theorem dual_delta {n : ℕ} (i : Fin (n + 2)) :
    dual.map (δ i) = (σ i).op := by
  simp [dual, δ, CategoryTheory.Quotient.lift_map_functor_map, Paths.of_map,
    Paths.lift_toPath, dualQuiver]

private theorem dual_sigma {n : ℕ} (i : Fin (n + 1)) :
    dual.map (σ i) = (δ i.succ.castSucc).op := by
  simp [dual, σ, CategoryTheory.Quotient.lift_map_functor_map, Paths.of_map,
    Paths.lift_toPath, dualQuiver]

private def shift : SimplexCategoryGenRel ⥤ SimplexCategoryGenRel :=
  dual ⋙ dual.leftOp

private theorem shift_delta {n : ℕ} (i : Fin (n + 2)) :
    shift.map (δ i) = δ i.succ.castSucc := by
  change (dual.map (dual.map (δ i)).unop).unop = _
  rw [dual_delta, Quiver.Hom.unop_op, dual_sigma, Quiver.Hom.unop_op]

private theorem dual_of_delta {a b : SimplexCategoryGenRel} {f : a ⟶ b} (hf : P_δ f) :
    P_σ (dual.map f).unop := by
  induction hf with
  | of f h => cases h; rw [dual_delta, Quiver.Hom.unop_op]; exact P_σ.σ _
  | id n => change P_σ (𝟙 _); exact P_σ.id_mem _
  | comp_of f g hf hg ih =>
    cases hg
    rw [Functor.map_comp, unop_comp, dual_delta, Quiver.Hom.unop_op]
    exact P_σ.comp_mem _ _ (P_σ.σ _) ih

private theorem dual_map_commutes {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    toSimplexCategory.map (dual.map f).unop =
      (SimplexCategory.II.map (toSimplexCategory.map f)).unop := by
  induction f with
  | @id n =>
    rw [dual.map_id (mk n), unop_id, toSimplexCategory.map_id,
      toSimplexCategory.map_id, SimplexCategory.II.map_id, unop_id]
    rfl
  | comp_δ f i ih =>
    rw [Functor.map_comp, Functor.map_comp, unop_comp, dual_delta,
      Quiver.Hom.unop_op, Functor.map_comp, Functor.map_comp, ih]
    simp only [toSimplexCategory_map_δ, toSimplexCategory_map_σ,
      unop_comp]
    rw [show SimplexCategory.II.map (SimplexCategory.δ i) = (SimplexCategory.σ i).op from
      SimplexCategory.II_δ i]
    rfl
  | comp_σ f i ih =>
    rw [Functor.map_comp, Functor.map_comp, unop_comp, dual_sigma,
      Quiver.Hom.unop_op, Functor.map_comp, Functor.map_comp, ih]
    simp only [toSimplexCategory_map_σ, toSimplexCategory_map_δ,
      unop_comp]
    rw [show SimplexCategory.II.map (SimplexCategory.σ i) =
      (SimplexCategory.δ i.succ.castSucc).op from SimplexCategory.II_σ i]
    rfl

private def embed (n : ℕ) : mk n ⟶ shift.obj (mk n) :=
  δ (Fin.last (n + 1)) ≫ δ (0 : Fin (n + 3))

private theorem embed_delta {n : ℕ} (i : Fin (n + 2)) :
    δ i ≫ embed (n + 1) = embed n ≫ shift.map (δ i) := by
  rw [shift_delta]
  change δ i ≫ (δ (Fin.last (n + 2)) ≫ δ 0) =
    (δ (Fin.last (n + 1)) ≫ δ 0) ≫ δ i.succ.castSucc
  have h1 : δ i ≫ δ (Fin.last (n + 2)) = δ (Fin.last (n + 1)) ≫ δ i.castSucc := by
    simpa only [Fin.succ_last] using δ_comp_δ (Fin.le_last i)
  have h2 : δ i.castSucc ≫ δ (0 : Fin (n + 4)) =
      δ (0 : Fin (n + 3)) ≫ δ i.succ.castSucc := by
    simpa only [Fin.castSucc_zero, Fin.castSucc_succ] using
      (δ_comp_δ (i := (0 : Fin (n + 3))) (j := i.castSucc) (Fin.zero_le _)).symm
  rw [← Category.assoc, h1, Category.assoc, h2, ← Category.assoc]

private theorem embed_natural {a b : SimplexCategoryGenRel} {f : a ⟶ b} (hf : P_δ f) :
    f ≫ embed b.len = embed a.len ≫ shift.map f := by
  induction hf with
  | of f h => cases h; exact embed_delta _
  | id n =>
    rw [shift.map_id n, Category.id_comp]
    cases n using SimplexCategoryGenRel.rec
    exact (Category.comp_id (embed _)).symm
  | comp_of f g hf hg ih =>
    cases hg
    simp only [mk_len] at ih ⊢
    rw [Functor.map_comp, Category.assoc, embed_delta, ← Category.assoc, ih, Category.assoc]


private theorem sigma_lists_eq {n m : ℕ} {L K : List ℕ}
    (hL : IsAdmissible m L) (hK : IsAdmissible m K)
    (hl : m + L.length = n) (hk : m + K.length = n)
    (he : toSimplexCategory.map (standardσ L hl) =
      toSimplexCategory.map (standardσ K hk)) : L = K := by
  have hval (j : ℕ) (hj : j < n + 1) : simplicialEvalσ L j = simplicialEvalσ K j := by
    rw [← simplicialEvalσ_of_isAdmissible L n m hL hl j hj,
      ← simplicialEvalσ_of_isAdmissible K n m hK hk j hj, he]
  apply hL.sortedLT.eq_of_mem_iff hK.sortedLT
  intro j
  rw [mem_isAdmissible_iff L hL, mem_isAdmissible_iff K hK, hl, hk]
  by_cases hj : j < n
  · rw [hval j (by omega), hval (j + 1) (by omega)]
  · simp [hj]

private theorem sigma_injective {a b : SimplexCategoryGenRel} {f g : a ⟶ b}
    (hf : P_σ f) (hg : P_σ g) (he : toSimplexCategory.map f = toSimplexCategory.map g) :
    f = g := by
  obtain ⟨L, m, k, hb, ha, hl, hL, ef⟩ := exists_normal_form_P_σ f hf
  obtain ⟨K, m', k', hb', ha', hk, hK, eg⟩ := exists_normal_form_P_σ g hg
  have hmm : m = m' := by
    have h := congrArg SimplexCategoryGenRel.len (hb.trans hb'.symm)
    simpa using h
  subst m'
  have hkk : k = k' := by
    have h := congrArg SimplexCategoryGenRel.len (ha.symm.trans ha')
    simp only [mk_len] at h
    omega
  subst k'
  subst b
  subst a
  have hLK : L = K := sigma_lists_eq (n := m + k) hL hK (by omega) (by omega) (by
    rw [ef, eg] at he
    exact he)
  subst K
  exact ef.trans eg.symm

private theorem epi_mono_unique {a b z : SimplexCategory}
    (e e' : a ⟶ z) (m m' : z ⟶ b) [Epi e] [Epi e'] [Mono m] [Mono m']
    (he : e ≫ m = e' ≫ m') : e = e' ∧ m = m' := by
  generalize hf : e ≫ m = f at *
  have hz : image f = z := SimplexCategory.image_eq hf
  subst z
  have hm : image.ι f = m := SimplexCategory.image_ι_eq hf
  have hm' : image.ι f = m' := SimplexCategory.image_ι_eq he.symm
  have hmm : m = m' := hm.symm.trans hm'
  refine ⟨?_, hmm⟩
  apply (cancel_mono m).mp
  rw [hf]
  simpa only [← hmm] using he


private theorem coface_injective {a b : SimplexCategoryGenRel} {f g : a ⟶ b}
    (hf : P_δ f) (hg : P_δ g) (he : toSimplexCategory.map f = toSimplexCategory.map g) :
    f = g := by
  have hd : dual.map f = dual.map g := by
    apply Quiver.Hom.unop_inj
    apply sigma_injective (dual_of_delta hf) (dual_of_delta hg)
    rw [dual_map_commutes, dual_map_commutes, he]
  have hs : shift.map f = shift.map g := by
    change (dual.map (dual.map f).unop).unop = (dual.map (dual.map g).unop).unop
    rw [hd]
  have : Mono (embed b.len) := by
    dsimp only [embed]
    infer_instance
  apply (cancel_mono (embed b.len)).mp
  rw [embed_natural hf, embed_natural hg, hs]


/-- The canonical presentation functor is faithful.
Source: Stacks Project, Tag 0168, Lemma 14.2.4(c); Kerodon, Propositions
1.1.1.9 and 1.1.2.13 (Tags 04FQ and 04FT) for the two pure normal forms.
(blueprint: lem-sc-module-cup-godement-simplex-presentation-faithful)
Proof: factor each word as a pure sigma block followed by a pure delta block,
using Mathlib's factorization theorem. Equal monotone maps have the same image,
so the middle ordinals agree. Uniqueness of epi-mono factorizations then shows
that both blocks have equal monotone maps. For sigma blocks use the existing
normal form: its increasing admissible list is determined by the adjacent
indices where evaluation agrees, hence equal maps give equal sorted lists.
For delta blocks use order duality: on the presentation it sends delta_i to
sigma_i and sigma_i to delta_(i+1), in the opposite category and one degree
higher. Check its six relations directly and lift it through the quotient.
It commutes with Mathlib's order-duality functor II. Duals of pure coface
words are pure sigma words, hence equal maps have equal duals by sigma
injectivity. The double dual shifts degree by two and inserts both endpoints;
the resulting embedding is natural on pure coface words and is a split mono.
Apply the dual again and cancel this embedding to recover equality of the
coface words. Both blocks, and therefore their composites, are equal. Empty
blocks, identities and [0] are covered by these same inductions. The duality
argument is written by H1 using Mathlib's II construction, rather than leaving
the missing pure-delta normal forms as an assumption. -/
theorem simplexPresentation_faithful :
    SimplexCategoryGenRel.toSimplexCategory.Faithful := by
  constructor
  intro a b f g he
  obtain ⟨z, e, m, heσ, hmδ, hfac⟩ := exists_P_σ_P_δ_factorization f
  obtain ⟨z', e', m', he'σ, hm'δ, hfac'⟩ := exists_P_σ_P_δ_factorization g
  have := isSplitEpi_toSimplexCategory_map_of_P_σ heσ
  have := isSplitMono_toSimplexCategory_map_of_P_δ hmδ
  have := isSplitEpi_toSimplexCategory_map_of_P_σ he'σ
  have := isSplitMono_toSimplexCategory_map_of_P_δ hm'δ
  have h1 : toSimplexCategory.map e ≫ toSimplexCategory.map m = toSimplexCategory.map f := by
    rw [← Functor.map_comp, ← hfac]
  have h2 : toSimplexCategory.map e' ≫ toSimplexCategory.map m' = toSimplexCategory.map f := by
    rw [← Functor.map_comp, ← hfac', he]
  have hz : z = z' := by
    apply SimplexCategoryGenRel.ext
    have h := congrArg SimplexCategory.len
      ((SimplexCategory.image_eq h1).symm.trans (SimplexCategory.image_eq h2))
    exact h
  subst z'
  have hem := epi_mono_unique (toSimplexCategory.map e) (toSimplexCategory.map e')
    (toSimplexCategory.map m) (toSimplexCategory.map m') (h1.trans h2.symm)
  have hee : e = e' := sigma_injective heσ he'σ hem.1
  have hmm : m = m' := coface_injective hmδ hm'δ hem.2
  rw [hfac, hfac', hee, hmm]


end
