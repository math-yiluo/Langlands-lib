import Langlands.Cohomology.CechCup
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Pullback of Čech cochains of structure sheaves along morphisms of schemes

Let `f : X ⟶ Y` be a morphism of schemes, `U` a family of opens of `Y`, `U'` a family of opens of
`X` and `α` a map of index types with `U' i ≤ f⁻¹ (U (α i))`. Pulling back sections along `f`
gives a map from the ordered Čech cochains of `𝒪_Y` for `U` to those of `𝒪_X` for `U'`,
`(pull c) σ = f^♯ (c (α ∘ σ))`. It commutes with the Čech differential and with products of
one-cochains, and is compatible with composition. Two index maps for the same morphism give
pullbacks of a `1`-cocycle that differ by a coboundary.
-/

universe w w' w'' u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Langlands.Cohomology.Cech

lemma mem_inter {T : TopCat.{u}} {ι : Type w} {U : ι → Opens T} {n : ℕ} (σ : Fin n → ι)
    (x : T) : x ∈ inter U σ ↔ ∀ a, x ∈ U (σ a) := by
  rw [← SetLike.mem_coe, inter, Opens.coe_iInf, Set.mem_iInter]
  rfl

section Pullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type w} {ι' : Type w'} {U : ι → Y.Opens}
  {U' : ι' → X.Opens} {α : ι' → ι}

lemma inter_le_preimage (hα : ∀ i, U' i ≤ f ⁻¹ᵁ U (α i)) {n : ℕ} (σ : Fin n → ι') :
    inter U' σ ≤ f ⁻¹ᵁ inter U (α ∘ σ) := by
  intro x hx
  rw [Scheme.Hom.mem_preimage, mem_inter]
  rw [mem_inter] at hx
  exact fun a => hα (σ a) (hx a)

variable (U U' α) in
/-- The pullback of ordered Čech cochains of `𝒪_Y` along `f`, using the index map `α`. -/
def pull (hα : ∀ i, U' i ≤ f ⁻¹ᵁ U (α i)) (p : ℕ) :
    C (ab Y.presheaf) U p →+ C (ab X.presheaf) U' p where
  toFun c σ := (f.appLE (inter U (α ∘ σ)) (inter U' σ) (inter_le_preimage f hα σ)).hom (c (α ∘ σ))
  map_zero' := by
    funext σ
    exact map_zero (f.appLE (inter U (α ∘ σ)) (inter U' σ) (inter_le_preimage f hα σ)).hom
  map_add' c c' := by
    funext σ
    exact map_add (f.appLE (inter U (α ∘ σ)) (inter U' σ) (inter_le_preimage f hα σ)).hom _ _

variable (hα : ∀ i, U' i ≤ f ⁻¹ᵁ U (α i))

lemma pull_apply (p : ℕ) (c : C (ab Y.presheaf) U p) (σ : Fin (p + 1) → ι') :
    pull f U U' α hα p c σ =
      (f.appLE (inter U (α ∘ σ)) (inter U' σ) (inter_le_preimage f hα σ)).hom (c (α ∘ σ)) :=
  rfl

lemma res_appLE {V : Y.Opens} {W W' : X.Opens} (h : W' ≤ W) (e : W ≤ f ⁻¹ᵁ V)
    (x : Γ(Y, V)) :
    res (P := ab X.presheaf) h ((f.appLE V W e).hom x) = (f.appLE V W' (h.trans e)).hom x := by
  change (f.appLE V W e ≫ X.presheaf.map (homOfLE h).op).hom x = _
  rw [Scheme.Hom.appLE_map]

lemma appLE_res {V V' : Y.Opens} {W : X.Opens} (h : V' ≤ V) (e : W ≤ f ⁻¹ᵁ V')
    (x : Γ(Y, V)) :
    (f.appLE V' W e).hom (res (P := ab Y.presheaf) h x) =
      (f.appLE V W (e.trans (f.preimage_mono h))).hom x := by
  change (Y.presheaf.map (homOfLE h).op ≫ f.appLE V' W e).hom x = _
  rw [Scheme.Hom.map_appLE]

/-- Pulling back sections indexed by equal tuples. -/
lemma appLE_congr_idx {n : ℕ} (x : ∀ σ : Fin n → ι, (ab Y.presheaf).obj (op (inter U σ)))
    {σ σ' : Fin n → ι} (h : σ = σ') {W : X.Opens} (e : W ≤ f ⁻¹ᵁ inter U σ)
    (e' : W ≤ f ⁻¹ᵁ inter U σ') :
    (f.appLE (inter U σ) W e).hom (x σ) = (f.appLE (inter U σ') W e').hom (x σ') := by
  subst h
  rfl

lemma face_pull (p : ℕ) (c : C (ab Y.presheaf) U p) {n : ℕ} (τ : Fin n → ι')
    (θ : Fin (p + 1) → Fin n) :
    face (pull f U U' α hα p c) τ θ =
      (f.appLE (inter U (α ∘ τ)) (inter U' τ) (inter_le_preimage f hα τ)).hom
        (face c (α ∘ τ) θ) := by
  rw [face, pull_apply, res_appLE, face, appLE_res]
  rfl

lemma d_pull (p : ℕ) (c : C (ab Y.presheaf) U p) :
    d (ab X.presheaf) U' p (pull f U U' α hα p c) =
      pull f U U' α hα (p + 1) (d (ab Y.presheaf) U p c) := by
  funext τ
  rw [d_apply_face, pull_apply, d_apply_face, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [face_pull, map_zsmul]

lemma pull_prod (n : ℕ) (z : Fin n → C (ab Y.presheaf) U 1) :
    pull f U U' α hα n (prod Y.presheaf U n z) =
      prod X.presheaf U' n (fun k => pull f U U' α hα 1 (z k)) := by
  funext τ
  rw [pull_apply, prod_apply, prod_apply, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [face_pull]

lemma pull_one : pull f U U' α hα 0 (one Y.presheaf U) = one X.presheaf U' := by
  funext τ
  exact map_one (f.appLE (inter U (α ∘ τ)) (inter U' τ) (inter_le_preimage f hα τ)).hom

lemma pull_comp {Z : Scheme.{u}} (g : Y ⟶ Z) {ι'' : Type w''} {U'' : ι'' → Z.Opens}
    {β : ι → ι''} (hβ : ∀ i, U i ≤ g ⁻¹ᵁ U'' (β i)) (p : ℕ) (c : C (ab Z.presheaf) U'' p) :
    pull f U U' α hα p (pull g U'' U β hβ p c) =
      pull (f ≫ g) U'' U' (β ∘ α)
        (fun i => (hα i).trans (f.preimage_mono (hβ (α i)))) p c := by
  funext σ
  rw [pull_apply, pull_apply, pull_apply]
  change (g.appLE _ _ _ ≫ f.appLE _ _ _).hom _ = _
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl

end Pullback

section IndexChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type w} {ι' : Type w'} {U : ι → Y.Opens}
  {U' : ι' → X.Opens} {α α' : ι' → ι} (hα : ∀ i, U' i ≤ f ⁻¹ᵁ U (α i))
  (hα' : ∀ i, U' i ≤ f ⁻¹ᵁ U (α' i))

lemma le_preimage_inter_two {a b : ι} {V : X.Opens} (ha : V ≤ f ⁻¹ᵁ U a)
    (hb : V ≤ f ⁻¹ᵁ U b) : V ≤ f ⁻¹ᵁ inter U ![a, b] := by
  rw [inter_two]
  exact le_inf ha hb

variable (U U') in
/-- The `0`-cochain comparing the pullbacks of a `1`-cochain along two index maps. -/
def indexChange (z : C (ab Y.presheaf) U 1) : C (ab X.presheaf) U' 0 :=
  fun τ => (f.appLE (inter U ![α' (τ 0), α (τ 0)]) (inter U' τ)
    (le_preimage_inter_two f ((inter_le_apply τ 0).trans (hα' (τ 0)))
      ((inter_le_apply τ 0).trans (hα (τ 0))))).hom (z ![α' (τ 0), α (τ 0)])

/-- The pullbacks of a `1`-cocycle along two index maps for the same morphism differ by a
coboundary. -/
lemma pull_sub_pull_eq_d {z : C (ab Y.presheaf) U 1} (hz : d (ab Y.presheaf) U 1 z = 0) :
    pull f U U' α hα 1 z - pull f U U' α' hα' 1 z =
      d (ab X.presheaf) U' 0 (indexChange f U U' hα hα' z) := by
  funext τ
  have hτ : ∀ i, inter U' τ ≤ f ⁻¹ᵁ U (α (τ i)) := fun i => (inter_le_apply τ i).trans (hα _)
  have hτ' : ∀ i, inter U' τ ≤ f ⁻¹ᵁ U (α' (τ i)) := fun i => (inter_le_apply τ i).trans (hα' _)
  set O := f ⁻¹ᵁ (U (α (τ 0)) ⊓ U (α (τ 1)) ⊓ U (α' (τ 0)) ⊓ U (α' (τ 1))) with hO
  have hVO : inter U' τ ≤ O :=
    le_inf (le_inf (le_inf (hτ 0) (hτ 1)) (hτ' 0)) (hτ' 1)
  set O' := U (α (τ 0)) ⊓ U (α (τ 1)) ⊓ U (α' (τ 0)) ⊓ U (α' (τ 1))
  have l : ∀ {a b : ι}, O' ≤ U a → O' ≤ U b → O' ≤ inter U ![a, b] := fun ha hb => by
    rw [inter_two]
    exact le_inf ha hb
  have l00 : O' ≤ U (α (τ 0)) := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have l01 : O' ≤ U (α (τ 1)) := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have l10 : O' ≤ U (α' (τ 0)) := inf_le_left.trans inf_le_right
  have l11 : O' ≤ U (α' (τ 1)) := inf_le_right
  have k₁ := cocycle_add hz (α' (τ 0)) (α (τ 0)) (α (τ 1)) (l l10 l00) (l l00 l01) (l l10 l01)
  have k₂ := cocycle_add hz (α' (τ 0)) (α' (τ 1)) (α (τ 1)) (l l10 l11) (l l11 l01) (l l10 l01)
  have e : inter U' τ ≤ f ⁻¹ᵁ O' := hVO
  have m₁ := congrArg (f.appLE O' (inter U' τ) e).hom k₁
  have m₂ := congrArg (f.appLE O' (inter U' τ) e).hom k₂
  simp only [map_add, appLE_res] at m₁ m₂
  rw [Pi.sub_apply, pull_apply, pull_apply, d_apply_face, Fin.sum_univ_two]
  simp only [face, indexChange, res_appLE, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_smul]
  rw [appLE_congr_idx f z (σ := α ∘ τ) (σ' := ![α (τ 0), α (τ 1)])
      (by funext i; fin_cases i <;> rfl) _ (e.trans (f.preimage_mono (l l00 l01))),
    appLE_congr_idx f z (σ := α' ∘ τ) (σ' := ![α' (τ 0), α' (τ 1)])
      (by funext i; fin_cases i <;> rfl) _ (e.trans (f.preimage_mono (l l10 l11))),
    appLE_congr_idx f z (σ := ![α' ((τ ∘ Fin.succAbove 0) 0), α ((τ ∘ Fin.succAbove 0) 0)])
      (σ' := ![α' (τ 1), α (τ 1)]) (by rfl) _ (e.trans (f.preimage_mono (l l11 l01))),
    appLE_congr_idx f z (σ := ![α' ((τ ∘ Fin.succAbove 1) 0), α ((τ ∘ Fin.succAbove 1) 0)])
      (σ' := ![α' (τ 0), α (τ 0)]) (by rfl) _ (e.trans (f.preimage_mono (l l10 l00)))]
  linear_combination (exp := 1) m₁ - m₂

end IndexChange

end Langlands.Cohomology.Cech
