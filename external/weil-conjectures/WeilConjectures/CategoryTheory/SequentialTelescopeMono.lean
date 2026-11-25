/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# Monicity of the sequential telescope map

Source: Stacks Project, Derived Categories, Tag 093W, `lemma-compute-colimit`.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CoproductsFromFiniteFiltered

namespace CategoryTheory

attribute [local instance] Abelian.hasFiniteBiproducts IsFiltered.isConnected

private noncomputable def telescopeCoordinate
    {A : Type u} [Category.{v} A] [Abelian A]
    (E : ℕ ⥤ A) (B : Cofan (fun n : ℕ ↦ E.obj n)) (hB : IsColimit B)
    (i : ℕ) : B.pt ⟶ E.obj i := by
  classical
  exact hB.desc (Cofan.mk _ (fun k ↦ if h : k ≤ i then E.map (homOfLE h) else 0))

private theorem inj_telescopeCoordinate
    {A : Type u} [Category.{v} A] [Abelian A]
    (E : ℕ ⥤ A) (B : Cofan (fun n : ℕ ↦ E.obj n)) (hB : IsColimit B)
    (i k : ℕ) : B.inj k ≫ telescopeCoordinate E B hB i =
      if h : k ≤ i then E.map (homOfLE h) else 0 := by
  classical
  exact hB.fac _ ⟨k⟩

private theorem inj_telescope_coordinate
    {A : Type u} [Category.{v} A] [Abelian A]
    (E : ℕ ⥤ A) (B : Cofan (fun n : ℕ ↦ E.obj n)) (hB : IsColimit B)
    (t : B.pt ⟶ B.pt)
    (ht : ∀ n : ℕ, B.inj n ≫ t =
      B.inj n - E.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1))
    (i k : ℕ) : (B.inj k ≫ t) ≫ telescopeCoordinate E B hB i =
      if h : k = i then eqToHom (congrArg E.obj h) else 0 := by
  classical
  rw [ht, Preadditive.sub_comp, Category.assoc,
    inj_telescopeCoordinate, inj_telescopeCoordinate]
  by_cases h : k = i
  · subst i
    simp [show ¬ k + 1 ≤ k by omega]
  · by_cases hki : k ≤ i
    · have hki' : k + 1 ≤ i := by omega
      simp only [dite_eq_left hki, dite_eq_left hki', dite_eq_right h, ← E.map_comp]
      exact sub_self _
    · have hki' : ¬ k + 1 ≤ i := by omega
      simp [hki, hki', h]

/-- The map given on the nth coprojection by identity minus the next transition is monic.
Source: Stacks Project, Derived Categories, Tag 093W, `lemma-compute-colimit`.
(auxiliary; not a blueprint node).

Proof: Regard the coproduct as the filtered colimit of its finite subcoproducts.
For each finite subset S and i in S, map the whole coproduct to E_i by the transition
E_k to E_i when k is at most i, and zero otherwise. Composing this map with the
telescope map on E_k gives identity if k=i and zero otherwise: the two transition
maps cancel when k<i. Their finite product therefore retracts the restriction of
the telescope map to the finite sum indexed by S. Each restriction is consequently
monic. Exactness of filtered colimits carries this diagram of monomorphisms into
the constant target coproduct to a monomorphism on its colimit, which is precisely
the original telescope map. The empty finite subset has zero source, and the
coordinate calculation does not assume that any transition map is monic. -/
theorem sequentialTelescope_mono
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasFilteredColimitsOfSize.{0, 0} A] [AB5OfSize.{0, 0} A]
    (E : ℕ ⥤ A) (B : Cofan (fun n : ℕ ↦ E.obj n)) (hB : IsColimit B)
    (t : B.pt ⟶ B.pt)
    (ht : ∀ n : ℕ, B.inj n ≫ t =
      B.inj n - E.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1)) : Mono t := by
  classical
  let K : ℕ → A := fun n ↦ E.obj n
  have : HasCoproduct K := ⟨⟨B, hB⟩⟩
  let e : (∐ K) ≅ B.pt := (colimit.isColimit _).coconePointUniqueUpToIso hB
  let c := finiteSubcoproductsCocone K
  let F := liftToFinsetObj (Discrete.functor K)
  let cB : Cocone F :=
    { pt := B.pt
      ι := { app S := c.ι.app S ≫ e.hom
             naturality i j f := by
               change F.map f ≫ (c.ι.app j ≫ e.hom) = (c.ι.app i ≫ e.hom) ≫ 𝟙 _
               rw [Category.comp_id, ← Category.assoc, c.w f] } }
  have hcB : IsColimit cB :=
    (isColimitFiniteSubproductsCocone K).ofIsoColimit
      (Cocone.ext e (fun S ↦ rfl))
  let φ : F ⟶ (Functor.const _).obj B.pt :=
    { app S := cB.ι.app S ≫ t
      naturality i j f := by
        change F.map f ≫ (cB.ι.app j ≫ t) = (cB.ι.app i ≫ t) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, cB.w f] }
  have hmono (S : Finset (Discrete ℕ)) : Mono (φ.app S) := by
    let r : B.pt ⟶ ⨁ (fun i : S ↦ E.obj i.val.as) :=
      biproduct.lift (fun i : S ↦ telescopeCoordinate E B hB i.val.as)
    have hr : φ.app S ≫ r =
        (biproduct.isoCoproduct (fun i : S ↦ E.obj i.val.as)).inv := by
      apply Sigma.hom_ext
      intro k
      apply biproduct.hom_ext
      intro i
      have hk : Sigma.ι (fun j : S ↦ E.obj j.val.as) k ≫ cB.ι.app S =
          B.inj k.val.as := by
        change Sigma.ι (fun j : S ↦ E.obj j.val.as) k ≫
          (Sigma.desc (fun j : S ↦ Sigma.ι K j.val.as) ≫ e.hom) = _
        rw [← Category.assoc, Sigma.ι_comp_desc]
        exact IsColimit.comp_coconePointUniqueUpToIso_hom
          (colimit.isColimit _) hB (Discrete.mk k.val.as)
      change (Sigma.ι (fun j : S ↦ E.obj j.val.as) k ≫
        ((cB.ι.app S ≫ t) ≫ r)) ≫ biproduct.π _ i = _
      rw [Category.assoc, Category.assoc, Category.assoc, biproduct.lift_π]
      rw [← Category.assoc, ← Category.assoc, hk, inj_telescope_coordinate E B hB t ht]
      rw [biproduct.isoCoproduct_inv, Sigma.ι_comp_desc]
      by_cases h : k = i
      · subst i
        simp
      · have h' : k.val.as ≠ i.val.as := by
          intro h'
          exact h (Subtype.ext (Discrete.ext h'))
        simp [h, h']
    have : Mono (φ.app S ≫ r) := by rw [hr]; infer_instance
    exact mono_of_mono (φ.app S) r
  have : Mono φ := NatTrans.mono_of_mono_app φ
  exact colim.map_mono' φ hcB (isColimitConstCocone _ _) t (by
    intro S
    change cB.ι.app S ≫ t = (cB.ι.app S ≫ t) ≫ 𝟙 _
    rw [Category.comp_id])

end CategoryTheory
