/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.ProEtaleRepresentableEpiLocalLifting

/-! # Local lifting of matching data on a pro-etale hypercover
Source: Stacks Project, Tags 0186, 00WN, 01GE and 01GW.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

/-- The underlying augmentation of a simplicial object in a slice category.
Source: Stacks Project, Tag 01GE.
(auxiliary; not a blueprint node). -/
def hypercoverUnderlyingAugmentation (X : Scheme.{u}) (W : X.ProEt)
    (U : SimplicialObject (Over W)) :
    U ⋙ Over.forget W ⟶ (Functor.const _).obj W where
  app Δ := (U.obj Δ).hom
  naturality _ _ f := by
    change (U.map f).left ≫ (U.obj _).hom = (U.obj _).hom ≫ 𝟙 _
    rw [Category.comp_id]
    exact (U.map f).w

private theorem lower_simplex_eq_of_faces {C : Type*} [Category* C]
    (U : SimplicialObject C) (n : ℕ) (T : C)
    (p : ∀ (Δ : SimplexCategory), Δ.len < n + 1 →
      (Δ ⟶ SimplexCategory.mk (n + 1)) → (T ⟶ U.obj (op Δ)))
    (hc : ∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n + 1)
      (h' : Δ'.len < n + 1) (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk (n + 1)),
      p Δ h θ ≫ U.map α.op = p Δ' h' (α ≫ θ))
    (t : T ⟶ U _⦋n + 1⦌)
    (ht : ∀ i : Fin (n + 2), t ≫ U.δ i = p (SimplexCategory.mk n) (by simp)
      (SimplexCategory.δ i)) :
    ∀ (Δ : SimplexCategory) (h : Δ.len < n + 1)
      (θ : Δ ⟶ SimplexCategory.mk (n + 1)), t ≫ U.map θ.op = p Δ h θ := by
  intro Δ h θ
  obtain ⟨i, θ', hθ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective θ (by
    intro hs
    have hh := Fintype.card_le_of_surjective θ.toOrderHom hs
    simp only [Fintype.card_fin] at hh
    have : Δ.len + 1 < n + 2 := by omega
    exact (not_le.mpr this) hh)
  rw [hθ, op_comp, U.map_comp, ← Category.assoc]
  change (t ≫ U.δ i) ≫ U.map θ'.op = _
  rw [ht]
  exact hc _ _ (by simp) h θ' (SimplexCategory.δ i)

set_option backward.isDefEq.respectTransparency false in
/-- Epimorphic matching maps supply local lifts of all compatible lower-simplex data.
Source: Stacks Project, Tags 0186 and 00WN, used in Tags 01GE and 01GW.
(auxiliary; not a blueprint node).

Proof: regard w:T→W and its compatible lower-simplex maps as objects and morphisms
of the slice over W. In degree zero lift w locally along U_0→W. In degree one the
two vertices define a map into the supplied limiting fan. In degree n+2 the
codimension-one entries satisfy the face-pair equations by compatibility and the
simplicial identities, so define a map into the supplied limiting multicospan.
Each matching epimorphism is locally surjective on represented sheaves; pull its
covering image sieve back along that map, and choose a lift on every member.
The face projection equations give the prescribed codimension-one maps. Any
operator from a smaller simplex misses a vertex, hence factors through one of
these faces (SimplexCategory.eq_comp_δ_of_not_surjective). Compatibility gives
its prescribed map as well. All lifted maps lie over w, giving the augmentation
equality. This works for empty test schemes and in degree zero, where the lower
simplex family is empty. The local-surjectivity step must respect the universe
of the representable sheaves in the displayed epi hypotheses. -/
theorem hypercover_matching_local_lifting
    (X : Scheme.{u}) (W : X.ProEt) (U : SimplicialObject (Over W))
    (hzero : Epi ((topology X).yoneda.map (U _⦋0⦌).hom))
    (hone : ∃ c : Fan (fun _ : Fin 2 ↦ U _⦋0⦌), Nonempty (IsLimit c) ∧
      ∃ μ : U _⦋1⦌ ⟶ c.pt,
        (∀ i : Fin 2, μ ≫ c.proj i = U.δ i) ∧
        Epi ((topology X).yoneda.map μ.left))
    (hhigher : ∀ n : ℕ,
      ∃ c : Cone (SimplicialObject.matchingBoundaryIndex U n).multicospan,
        Nonempty (IsLimit c) ∧ ∃ μ : U _⦋n + 2⦌ ⟶ c.pt,
          (∀ i : Fin (n + 3), μ ≫ c.π.app (WalkingMulticospan.left i) = U.δ i) ∧
          Epi ((topology X).yoneda.map μ.left)) :
    ∀ (n : ℕ) (T : X.ProEt) (w : T ⟶ W)
      (p : ∀ (Δ : SimplexCategory), Δ.len < n →
        (Δ ⟶ SimplexCategory.mk n) → (T ⟶ (U ⋙ Over.forget W).obj (op Δ))),
      (∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ (hypercoverUnderlyingAugmentation X W U).app (op Δ) = w) →
      (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
        (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ (U ⋙ Over.forget W).map α.op = p Δ' h' (α ≫ θ)) →
      ∃ S : Sieve T, S ∈ topology X T ∧
        ∀ (V : X.ProEt) (f : V ⟶ T), S f →
          ∃ t : V ⟶ (U ⋙ Over.forget W) _⦋n⦌,
            t ≫ (hypercoverUnderlyingAugmentation X W U).app
              (op (SimplexCategory.mk n)) = f ≫ w ∧
            ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
              t ≫ (U ⋙ Over.forget W).map θ.op = f ≫ p Δ h θ := by
  intro n T w p hp hc
  cases n with
  | zero =>
    obtain ⟨S, hS, hl⟩ := representable_epi_local_lifting X (U _⦋0⦌).hom hzero T w
    refine ⟨S, hS, ?_⟩
    intro V f hf
    obtain ⟨t, ht⟩ := hl V f hf
    refine ⟨t, ht, ?_⟩
    intro Δ h θ
    omega
  | succ n =>
    let x (i : Fin (n + 2)) : Over.mk w ⟶ U _⦋n⦌ :=
      Over.homMk (p (SimplexCategory.mk n) (by simp) (SimplexCategory.δ i))
        (hp _ (by simp) _)
    have hm : ∃ (M : Over W) (g : Over.mk w ⟶ M) (μ : U _⦋n + 1⦌ ⟶ M)
        (π : Fin (n + 2) → (M ⟶ U _⦋n⦌)),
        (∀ i, g ≫ π i = x i) ∧ (∀ i, μ ≫ π i = U.δ i) ∧
        Epi ((topology X).yoneda.map μ.left) := by
      cases n with
      | zero =>
        obtain ⟨c, ⟨hlim⟩, μ, hμ, hepi⟩ := hone
        refine ⟨c.pt, hlim.lift (Fan.mk (Over.mk w) x), μ, c.proj, ?_, hμ, hepi⟩
        intro i
        exact hlim.fac (Fan.mk (Over.mk w) x) ⟨i⟩
      | succ n =>
        obtain ⟨c, ⟨hlim⟩, μ, hμ, hepi⟩ := hhigher n
        have hx : ∀ j : (SimplicialObject.matchingBoundaryShape n).R,
            x j.val.1 ≫ (SimplicialObject.matchingBoundaryIndex U n).fst j =
              x j.val.2 ≫ (SimplicialObject.matchingBoundaryIndex U n).snd j := by
          intro j
          change {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2} at j
          apply Over.OverMorphism.ext
          let i := j.val.1.castLT (Nat.lt_of_lt_of_le j.property
            (Nat.le_of_lt_succ j.val.2.isLt))
          let k := j.val.2.pred (Fin.ne_zero_of_lt j.property)
          change p _ _ _ ≫ (U ⋙ Over.forget W).map (SimplexCategory.δ k).op =
            p _ _ _ ≫ (U ⋙ Over.forget W).map (SimplexCategory.δ i).op
          rw [hc _ _ (by simp) (by simp) _ _, hc _ _ (by simp) (by simp) _ _]
          congr 1
          exact (SimplexCategory.δ_comp_δ' (i := i) (j := j.val.2)
            (by change j.val.1 < j.val.2; exact j.property)).symm
        let cone := Multifork.ofι (SimplicialObject.matchingBoundaryIndex U n)
          (Over.mk w) x hx
        refine ⟨c.pt, hlim.lift cone, μ,
          fun i ↦ c.π.app (WalkingMulticospan.left i), ?_, hμ, hepi⟩
        intro i
        exact hlim.fac cone (WalkingMulticospan.left i)
    obtain ⟨M, g, μ, π, hg, hμ, hepi⟩ := hm
    obtain ⟨S, hS, hl⟩ := representable_epi_local_lifting X μ.left hepi T g.left
    refine ⟨S, hS, ?_⟩
    intro V f hf
    obtain ⟨t, ht⟩ := hl V f hf
    refine ⟨t, ?_, ?_⟩
    · change t ≫ (U _⦋n + 1⦌).hom = f ≫ w
      rw [← μ.w, ← Category.assoc, ht, Category.assoc, g.w]
      rfl
    · apply lower_simplex_eq_of_faces (U ⋙ Over.forget W) n V
        (fun Δ h θ ↦ f ≫ p Δ h θ)
      · intro Δ Δ' h h' α θ
        rw [Category.assoc, hc]
      · intro i
        change t ≫ (U.δ i).left = f ≫ p _ _ _
        rw [← hμ i]
        change t ≫ (μ.left ≫ (π i).left) = _
        rw [← Category.assoc, ht, Category.assoc]
        exact congrArg (fun z ↦ f ≫ z.left) (hg i)

end AlgebraicGeometry.Scheme.ProEt
