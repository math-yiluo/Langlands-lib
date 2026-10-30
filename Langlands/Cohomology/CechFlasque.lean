import Mathlib.Topology.Sheaves.Flasque
import Langlands.Cohomology.CechCochains

/-!
# Čech exactness for flasque sheaves

For a flasque sheaf of abelian groups `F` on a topological space and a finite family of opens
`U`, the ordered Čech complex of `F` for `U` is exact in every positive degree. No covering
condition is needed: the cocycle is killed on `⨆ j ∈ S, U j` by induction on the finite set `S`,
gluing over two opens and extending sections by flasqueness at each step.
-/

universe w u

open CategoryTheory Opposite TopologicalSpace

namespace Langlands.Cohomology.Cech

variable {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T)

/-- Any two sections of a sheaf over an open contained in `⊥` agree. -/
lemma eq_of_le_bot {O : Opens T} (hO : O ≤ ⊥) (s t : F.1.obj (op O)) : s = t :=
  F.eq_of_locally_eq' (fun k : PEmpty.{1} => k.elim) O (fun k => k.elim)
    (hO.trans (iSup_of_empty _).ge) s t (fun k => k.elim)

/-- Sections over `O₁ ⊔ O₂` are determined by their restrictions to `O₁` and `O₂`. -/
lemma eq_of_res_eq₂ {O₁ O₂ V : Opens T} (h₁ : O₁ ≤ V) (h₂ : O₂ ≤ V) (hV : V ≤ O₁ ⊔ O₂)
    (s t : F.1.obj (op V)) (e₁ : res h₁ s = res h₁ t) (e₂ : res h₂ s = res h₂ t) : s = t :=
  F.eq_of_locally_eq₂ (homOfLE h₁) (homOfLE h₂) hV s t e₁ e₂

/-- Two sections over `A` and `B` agreeing on `A ⊓ B` glue to a section over `A ⊔ B`. -/
lemma exists_glue₂ {A B : Opens T} (a : F.1.obj (op A)) (b : F.1.obj (op B))
    (h : res (inf_le_left : A ⊓ B ≤ A) a = res inf_le_right b) :
    ∃ c : F.1.obj (op (A ⊔ B)), res le_sup_left c = a ∧ res le_sup_right c = b := by
  let f : Fin 2 → Opens T := ![A, B]
  let sf : (k : Fin 2) → F.1.obj (op (f k))
    | 0 => a
    | 1 => b
  have hf : ∀ k, f k ≤ A ⊔ B := Fin.forall_fin_two.2 ⟨le_sup_left, le_sup_right⟩
  obtain ⟨c, hc, -⟩ := F.existsUnique_gluing' f (A ⊔ B) (fun k => homOfLE (hf k))
    (sup_le (le_iSup f 0) (le_iSup f 1)) sf (by
      simp only [TopCat.Presheaf.IsCompatible, Fin.forall_fin_two]
      refine ⟨⟨rfl, h⟩, ?_, rfl⟩
      have := congrArg (res (P := F.1) (le_of_eq (inf_comm B A))) h
      simp only [res_res] at this
      exact this.symm)
  exact ⟨c, hc 0, hc 1⟩

/-- Restriction maps of a flasque sheaf are surjective. -/
lemma surjective_res [TopCat.Presheaf.IsFlasque F.1] {V W : Opens T} (h : V ≤ W) :
    Function.Surjective (res (P := F.1) h) :=
  (AddCommGrpCat.epi_iff_surjective _).1 inferInstance

/-- The ordered Čech complex of a flasque sheaf for a finite family of opens is exact in
every positive degree. -/
theorem exactAt_of_isFlasque [TopCat.Presheaf.IsFlasque F.1] {ι : Type w} [Finite ι]
    (U : ι → Opens T) (p : ℕ) : ExactAt F.1 U p := by
  classical
  cases nonempty_fintype ι
  intro z hz
  have key : ∀ S : Finset ι, ∃ y : C F.1 U p, ∀ τ : Fin (p + 2) → ι,
      res (inf_le_right : (⨆ j ∈ S, U j) ⊓ inter U τ ≤ inter U τ)
        (z τ - d F.1 U p y τ) = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨0, fun τ => eq_of_le_bot F ?_ _ _⟩
      simp
    | insert i S hi ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨z', hz'⟩ : ∃ z', z' = z - d F.1 U p y := ⟨_, rfl⟩
      have hz'd : d F.1 U (p + 1) z' = 0 := by rw [hz', map_sub, hz, d_d, sub_zero]
      have hy' : ∀ τ, res (inf_le_right : (⨆ j ∈ S, U j) ⊓ inter U τ ≤ inter U τ)
          (z' τ) = 0 := by
        intro τ
        rw [hz']
        exact hy τ
      have hw : ∀ σ : Fin (p + 1) → ι, ∃ w : F.1.obj (op (inter U σ)),
          res (inf_le_right : U i ⊓ inter U σ ≤ inter U σ) w =
            res (inter_cons U i σ).ge (z' (Fin.cons i σ)) ∧
          res (inf_le_right : (⨆ j ∈ S, U j) ⊓ inter U σ ≤ inter U σ) w = 0 := by
        intro σ
        have hle : (U i ⊓ inter U σ) ⊓ ((⨆ j ∈ S, U j) ⊓ inter U σ) ≤
            (⨆ j ∈ S, U j) ⊓ inter U (Fin.cons i σ : Fin (p + 2) → ι) :=
          le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans (inter_cons U i σ).ge)
        obtain ⟨c, hc₁, hc₂⟩ := exists_glue₂ F
          (res (inter_cons U i σ).ge (z' (Fin.cons i σ)))
          (0 : F.1.obj (op ((⨆ j ∈ S, U j) ⊓ inter U σ))) (by
            have := congrArg (res hle) (hy' (Fin.cons i σ))
            rw [res_res, map_zero] at this
            rw [map_zero, res_res]
            exact this)
        obtain ⟨w, hw⟩ := surjective_res F
          (sup_le inf_le_right inf_le_right :
            (U i ⊓ inter U σ) ⊔ ((⨆ j ∈ S, U j) ⊓ inter U σ) ≤ inter U σ) c
        refine ⟨w, ?_, ?_⟩
        · rw [← hc₁, ← hw, res_res]
        · rw [← hc₂, ← hw, res_res]
      choose w hw₁ hw₂ using hw
      refine ⟨y + w, fun τ => ?_⟩
      have hzτ : z τ - d F.1 U p (y + w) τ = z' τ - d F.1 U p w τ := by
        rw [map_add, Pi.add_apply, hz', Pi.sub_apply]
        abel
      rw [hzτ]
      have h₁ : U i ⊓ inter U τ ≤ (⨆ j ∈ insert i S, U j) ⊓ inter U τ :=
        inf_le_inf_right _ (le_biSup U (Finset.mem_insert_self i S))
      have h₂ : (⨆ j ∈ S, U j) ⊓ inter U τ ≤ (⨆ j ∈ insert i S, U j) ⊓ inter U τ :=
        inf_le_inf_right _ (biSup_mono fun j hj => Finset.mem_insert_of_mem hj)
      have hcov : (⨆ j ∈ insert i S, U j) ⊓ inter U τ ≤
          (U i ⊓ inter U τ) ⊔ ((⨆ j ∈ S, U j) ⊓ inter U τ) := by
        rw [Finset.iSup_insert, inf_sup_right]
      refine eq_of_res_eq₂ F h₁ h₂ hcov _ _ ?_ ?_
      · rw [map_zero, res_res, map_sub, sub_eq_zero,
          res_eq_sum_of_d_eq_zero hz'd i τ le_rfl, d_apply, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, res_res]
        congr 1
        rw [← res_res (inf_le_inf_left (U i) (inter_le_comp τ k.succAbove)) inf_le_right, hw₁,
          res_res]
      · rw [map_zero, res_res, map_sub, hy' τ, zero_sub, neg_eq_zero, d_apply, map_sum]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [map_zsmul, res_res,
          ← res_res (inf_le_inf_left (⨆ j ∈ S, U j) (inter_le_comp τ k.succAbove)) inf_le_right,
          hw₂, map_zero, smul_zero]
  obtain ⟨y, hy⟩ := key Finset.univ
  refine ⟨y, funext fun τ => ?_⟩
  have hτ : inter U τ ≤ (⨆ j ∈ Finset.univ, U j) ⊓ inter U τ :=
    le_inf ((inter_le_apply τ 0).trans (le_biSup U (Finset.mem_univ _))) le_rfl
  have := congrArg (res hτ) (hy τ)
  rw [res_res, res_self, map_zero] at this
  exact (sub_eq_zero.1 this).symm

end Langlands.Cohomology.Cech
