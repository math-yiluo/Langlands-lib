import Langlands.Cohomology.CechCup
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.Grp.Limits

/-!
# Refinement of ordered Čech cochains

Let `U : ι → Opens T` and `U' : ι' → Opens T` be families of opens with `U' j ≤ U (β j)` for an
index map `β : ι' → ι`. Restricting `c (β ∘ σ)` to `U'_σ` defines the refinement map
`C(U, P) → C(U', P)` of ordered Čech cochains of a presheaf `P`. It commutes with the Čech
differential, with morphisms of presheaves and with composition of refinements.

For a sheaf `F` of abelian groups and a family `U'` covering the whole space, a `1`-cocycle on
`U` whose refinement to `U'` is a coboundary is already a coboundary on `U`. The primitive is
glued on each `U a` from the sections `c j - z (a, β j)` on `U a ⊓ U' j`.
-/

universe w w' v u

open CategoryTheory Opposite TopologicalSpace

namespace Langlands.Cohomology.Cech

section Refine

variable {T : TopCat.{u}} {P : TopCat.Presheaf AddCommGrpCat.{v} T} {ι : Type w} {ι' : Type w'}
  {U : ι → Opens T} {U' : ι' → Opens T} {β : ι' → ι}

lemma inter_le_inter_comp (hβ : ∀ j, U' j ≤ U (β j)) {n : ℕ} (σ : Fin n → ι') :
    inter U' σ ≤ inter U (β ∘ σ) :=
  le_iInf fun a => (inter_le_apply σ a).trans (hβ (σ a))

variable (P U U' β) in
/-- The refinement map of ordered Čech cochains for a family `U'` refining `U` through `β`. -/
def refine (hβ : ∀ j, U' j ≤ U (β j)) (p : ℕ) : C P U p →+ C P U' p where
  toFun c σ := res (inter_le_inter_comp hβ σ) (c (β ∘ σ))
  map_zero' := by
    funext σ
    exact map_zero _
  map_add' c c' := by
    funext σ
    exact map_add _ _ _

variable (hβ : ∀ j, U' j ≤ U (β j))

lemma refine_apply (p : ℕ) (c : C P U p) (σ : Fin (p + 1) → ι') :
    refine P U U' β hβ p c σ = res (inter_le_inter_comp hβ σ) (c (β ∘ σ)) :=
  rfl

lemma face_refine (p : ℕ) (c : C P U p) {n : ℕ} (τ : Fin n → ι') (θ : Fin (p + 1) → Fin n) :
    face (refine P U U' β hβ p c) τ θ = res (inter_le_inter_comp hβ τ) (face c (β ∘ τ) θ) := by
  rw [face, refine_apply, face, res_res, res_res]
  rfl

lemma d_refine (p : ℕ) (c : C P U p) :
    d P U' p (refine P U U' β hβ p c) = refine P U U' β hβ (p + 1) (d P U p c) := by
  funext τ
  rw [d_apply_face, refine_apply, d_apply_face, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [face_refine, map_zsmul]

lemma refine_comp {ι'' : Type*} {U'' : ι'' → Opens T} {γ : ι'' → ι'}
    (hγ : ∀ j, U'' j ≤ U' (γ j)) (p : ℕ) (c : C P U p) :
    refine P U' U'' γ hγ p (refine P U U' β hβ p c) =
      refine P U U'' (β ∘ γ) (fun j => (hγ j).trans (hβ (γ j))) p c := by
  funext σ
  simp only [refine_apply, res_res]
  rfl

lemma map_refine {Q : TopCat.Presheaf AddCommGrpCat.{v} T} (φ : P ⟶ Q) (p : ℕ) (c : C P U p) :
    map U' φ p (refine P U U' β hβ p c) = refine Q U U' β hβ p (map U φ p c) := by
  funext σ
  simp only [map, refine_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_res]

lemma refine_prod {R : TopCat.Presheaf CommRingCat.{v} T} (n : ℕ) (z : Fin n → C (ab R) U 1) :
    refine (ab R) U U' β hβ n (prod R U n z) =
      prod R U' n (fun k => refine (ab R) U U' β hβ 1 (z k)) := by
  funext τ
  rw [refine_apply, prod_apply, prod_apply, res_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [face_refine]

end Refine

section DegreeZero

variable {T : TopCat.{u}} {P : TopCat.Presheaf AddCommGrpCat.{v} T} {ι : Type w}
  {U : ι → Opens T}

lemma inter_const_one (a : ι) : inter U (fun _ : Fin 1 => a) = U a :=
  le_antisymm (inter_le_apply _ 0) (le_iInf fun _ => le_rfl)

/-- The Čech differential of a `0`-cochain on a pair `(a, b)`, restricted to a smaller open. -/
lemma res_d_zero_pair (y : C P U 0) (a b : ι) {O : Opens T} (h : O ≤ inter U ![a, b])
    (ha : O ≤ inter U (fun _ : Fin 1 => a)) (hb : O ≤ inter U (fun _ : Fin 1 => b)) :
    res h (d P U 0 y ![a, b]) = res hb (y (fun _ => b)) - res ha (y (fun _ => a)) := by
  rw [d_apply, Fin.sum_univ_two, map_add, map_zsmul, map_zsmul, res_res, res_res]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  rw [res_congr P U (σ := ![a, b] ∘ Fin.succAbove 0) (σ' := fun _ => b)
      (by funext i; fin_cases i; rfl) y _ hb,
    res_congr P U (σ := ![a, b] ∘ Fin.succAbove 1) (σ' := fun _ => a)
      (by funext i; fin_cases i; rfl) y _ ha]
  abel

end DegreeZero

section Sheaf

variable {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T)

/-- Sections of a sheaf agreeing on the members of a cover agree. -/
lemma eq_of_locally {V : Opens T} {κ : Type*} (W : κ → Opens T) (hW : ∀ k, W k ≤ V)
    (hcov : V ≤ iSup W) {x y : F.1.obj (op V)} (h : ∀ k, res (hW k) x = res (hW k) y) :
    x = y :=
  F.eq_of_locally_eq' W V (fun k => homOfLE (hW k)) hcov x y h

/-- Compatible sections of a sheaf on the members of a cover glue. -/
lemma exists_gluing {V : Opens T} {κ : Type*} (W : κ → Opens T) (hW : ∀ k, W k ≤ V)
    (hcov : V ≤ iSup W) (s : ∀ k, F.1.obj (op (W k)))
    (hs : ∀ k k', res (P := F.1) (inf_le_left : W k ⊓ W k' ≤ W k) (s k) =
      res (P := F.1) (inf_le_right : W k ⊓ W k' ≤ W k') (s k')) :
    ∃ x : F.1.obj (op V), ∀ k, res (hW k) x = s k := by
  obtain ⟨x, hx, -⟩ := F.existsUnique_gluing' W V (fun k => homOfLE (hW k)) hcov s hs
  exact ⟨x, hx⟩

variable {ι : Type w} {ι' : Type w'} {U : ι → Opens T} {U' : ι' → Opens T} {β : ι' → ι}
  (hβ : ∀ j, U' j ≤ U (β j))

lemma le_iSup_inf_of_top_le (hcov : ⊤ ≤ iSup U') (V : Opens T) : V ≤ ⨆ j, V ⊓ U' j := by
  intro x hx
  have hx' : x ∈ iSup U' := hcov (by trivial)
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hx'
  exact Opens.mem_iSup.2 ⟨j, ⟨hx, hj⟩⟩

/-- Degree-one refinement injectivity: if a family `U'` covers the space and refines `U`, a
`1`-cocycle of a sheaf on `U` whose refinement to `U'` is a coboundary is a coboundary. -/
theorem exists_d_eq_of_refine_eq_d (hcov : ⊤ ≤ iSup U') {z : C F.1 U 1}
    (hz : d F.1 U 1 z = 0) {c : C F.1 U' 0} (hc : refine F.1 U U' β hβ 1 z = d F.1 U' 0 c) :
    ∃ y : C F.1 U 0, d F.1 U 0 y = z := by
  have hU'1 : ∀ j, U' j ≤ inter U' (fun _ : Fin 1 => j) := fun j => (inter_const_one j).ge
  have l2 : ∀ {a b : ι} {O : Opens T}, O ≤ U a → O ≤ U b → O ≤ inter U ![a, b] :=
    fun ha hb => by
      rw [inter_two]
      exact le_inf ha hb
  have E1 : ∀ (j j' : ι') {O : Opens T} (h₁ : O ≤ U' j) (h₂ : O ≤ U' j'),
      res (l2 (h₂.trans (hβ j')) (h₁.trans (hβ j))) (z ![β j', β j]) =
        res (h₁.trans (hU'1 j)) (c (fun _ => j)) -
          res (h₂.trans (hU'1 j')) (c (fun _ => j')) := by
    intro j j' O h₁ h₂
    have hO : O ≤ inter U' ![j', j] := by
      rw [inter_two]
      exact le_inf h₂ h₁
    have e := congrArg (res hO) (congrFun hc ![j', j])
    rw [refine_apply, res_res,
      res_d_zero_pair c j' j hO (h₂.trans (hU'1 j')) (h₁.trans (hU'1 j))] at e
    rw [← e]
    exact res_congr _ _ (by funext i; fin_cases i <;> rfl) z _ _
  let s : ∀ a j, F.1.obj (op (U a ⊓ U' j)) := fun a j =>
    res (inf_le_right.trans (hU'1 j)) (c (fun _ => j)) -
      res (l2 inf_le_left (inf_le_right.trans (hβ j))) (z ![a, β j])
  have hs : ∀ a j j', res (P := F.1) (inf_le_left : (U a ⊓ U' j) ⊓ (U a ⊓ U' j') ≤ U a ⊓ U' j)
      (s a j) = res (P := F.1) (inf_le_right : (U a ⊓ U' j) ⊓ (U a ⊓ U' j') ≤ U a ⊓ U' j')
      (s a j') := by
    intro a j j'
    have hOa : (U a ⊓ U' j) ⊓ (U a ⊓ U' j') ≤ U a := inf_le_left.trans inf_le_left
    have hOj : (U a ⊓ U' j) ⊓ (U a ⊓ U' j') ≤ U' j := inf_le_left.trans inf_le_right
    have hOj' : (U a ⊓ U' j) ⊓ (U a ⊓ U' j') ≤ U' j' := inf_le_right.trans inf_le_right
    simp only [s, map_sub, res_res]
    have k := cocycle_add hz a (β j') (β j) (l2 hOa (hOj'.trans (hβ j')))
      (l2 (hOj'.trans (hβ j')) (hOj.trans (hβ j))) (l2 hOa (hOj.trans (hβ j)))
    rw [← k, E1 j j' hOj hOj']
    abel
  choose Y hY using fun a => exists_gluing F (fun j => U a ⊓ U' j) (fun j => inf_le_left)
    (le_iSup_inf_of_top_le hcov (U a)) (s a) (hs a)
  let y : C F.1 U 0 := fun σ => res (inter_le_apply σ 0) (Y (σ 0))
  have key : ∀ a b, d F.1 U 0 y ![a, b] = z ![a, b] := by
    intro a b
    apply eq_of_locally F (fun j => inter U ![a, b] ⊓ U' j) (fun j => inf_le_left)
      (le_iSup_inf_of_top_le hcov _)
    intro j
    have hOa : inter U ![a, b] ⊓ U' j ≤ U a := inf_le_left.trans (inter_le_apply ![a, b] 0)
    have hOb : inter U ![a, b] ⊓ U' j ≤ U b := inf_le_left.trans (inter_le_apply ![a, b] 1)
    have hOj : inter U ![a, b] ⊓ U' j ≤ U' j := inf_le_right
    rw [res_d_zero_pair y a b _ (hOa.trans (inter_const_one a).ge)
      (hOb.trans (inter_const_one b).ge)]
    simp only [y, res_res]
    rw [← res_res (le_inf hOb hOj) inf_le_left (Y b), hY b j,
      ← res_res (le_inf hOa hOj) inf_le_left (Y a), hY a j]
    simp only [s, map_sub, res_res]
    have k := cocycle_add hz a b (β j) (l2 hOa hOb) (l2 hOb (hOj.trans (hβ j)))
      (l2 hOa (hOj.trans (hβ j)))
    rw [← k]
    abel
  refine ⟨y, funext fun τ => ?_⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, τ = ![a, b] := ⟨τ 0, τ 1, by funext i; fin_cases i <;> rfl⟩
  exact key a b

end Sheaf

end Langlands.Cohomology.Cech
