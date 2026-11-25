/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechCriterion

/-!
# The Čech criterion with a chosen class of coverings and a lifting hypothesis

This file proves a variant of the Čech criterion
`CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex` ([Stacks, Tag 03F7]) in which
Čech exactness is only required for a chosen class `Good` of finite covering families, and the
hypothesis that every covering sieve contains such a family is replaced by the hypothesis that
sections of an epimorphism of abelian sheaves lift, over the members of `B`, after restriction to
the members of a family in `Good`.

## Main statements

- `CategoryTheory.Sheaf.surjective_app_of_exactAt_cechComplex_one_of_lift`: if a section of `Q`
  lifts to `I` locally on a finite covering family on which the first Čech cohomology of `F`
  vanishes, then it lifts to `I`, for a short exact sequence `0 → F → I → Q → 0`.
- `CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex_of_lift`: the criterion.
-/

@[expose] public section

universe w' v w

open CategoryTheory Limits Opposite

namespace CategoryTheory

namespace Sheaf

open Presheaf Abelian

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max w v}]

/-- Let `0 → F → I → Q → 0` be a short exact sequence of abelian sheaves and `s` a section of
`Q` over `V`. If there is a finite family `U` generating a covering sieve of `V`, on which the
first Čech cohomology of `F` vanishes and such that the restrictions of `s` to the members of `U`
lift to `I`, then `s` lifts to `I`. -/
theorem exists_app_g_eq_of_exactAt_cechComplex_one
    {S : ShortComplex (Sheaf J AddCommGrpCat.{max w v})} (hS : S.ShortExact) {V : C}
    [HasFiniteProducts (Over V)] (s : S.X₃.obj.obj (op V)) {n : ℕ} (U : Fin n → Over V)
    (hlift : ∀ a, ∃ t : S.X₂.obj.obj (op (U a).left),
      S.g.hom.app _ t = S.X₃.obj.map (U a).hom.op s)
    (hcov : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    (hU : ((cechComplex U).obj S.X₁.obj).ExactAt 1) :
    ∃ σ, S.g.hom.app (op V) σ = s := by
  choose t ht using hlift
  let a : ((cechComplex U).obj S.X₂.obj).X 0 := fun z ↦
    S.X₂.obj.map (Pi.π (fun l ↦ U (z l)) 0).left.op (t (z 0))
  have ha (z : Fin 1 → Fin n) : ((cechComplex U).map S.g.hom).f 0 a z =
      S.X₃.obj.map (cechNerveObj U z).hom.op s := by
    rw [cechComplex_map_f_apply, NatTrans.naturality_apply, ht, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, Over.w]
  obtain ⟨e, he⟩ := exists_cechComplex_map_f_eq U S.f.hom S.g.hom (exists_app_f_eq hS) _
    (((cechComplex U).obj S.X₂.obj).d 0 1 a) (by
      rw [cechComplex_map_f_d_apply]
      exact cechComplex_d_zero_restrict U _ s _ ha)
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff U _ 0).1 hU e
    (cechComplex_map_f_injective U _ (injective_app_f hS) _ (by
      rw [cechComplex_map_f_d_apply, he, map_zero, cechComplex_d_d_apply]))
  have hda : ((cechComplex U).obj S.X₂.obj).d 0 1
      (a - ((cechComplex U).map S.f.hom).f 0 b) = 0 := by
    rw [map_sub, ← cechComplex_map_f_d_apply, hb, he, sub_self]
  -- the members of the Čech nerve in degree `0` generate a covering sieve
  have hcov' : Sieve.ofArrows (fun z : Fin 1 → Fin n ↦ (cechNerveObj U z).left)
      (fun z ↦ (cechNerveObj U z).hom) ∈ J V := by
    refine J.superset_covering (fun Y g hg ↦ ?_) hcov
    obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    refine (Sieve.mem_ofArrows_iff _ _ _).2
      ⟨fun _ ↦ i, h ≫ (Pi.lift fun _ ↦ 𝟙 (U i)).left, ?_⟩
    rw [Category.assoc, Over.w]
  obtain ⟨σ, hσ, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (isSheafFor_ofArrows S.X₂ _ hcov') (fun z ↦ (a - ((cechComplex U).map S.f.hom).f 0 b) z)
    fun z z' Z g₁ g₂ hg ↦ map_eq_of_cechComplex_d_zero U _ _ hda z z' g₁ g₂ hg
  refine ⟨σ, (isSheafFor_ofArrows S.X₃ _ hcov').isSeparatedFor.ext fun Y f ⟨z⟩ ↦ ?_⟩
  change S.X₃.obj.map _ (S.g.hom.app _ σ) = S.X₃.obj.map _ s
  rw [← NatTrans.naturality_apply]
  erw [hσ z]
  rw [cechComplex_sub_apply, map_sub, cechComplex_map_f_apply, app_g_app_f, sub_zero, ← ha]
  rfl

/-- Let `0 → F → I → Q → 0` be a short exact sequence of abelian sheaves and `V` an object such
that every section of `Q` over `V` lifts to `I` after restriction to the members of a finite
family `U` generating a covering sieve, on which the first Čech cohomology of `F` vanishes. Then
`I(V) → Q(V)` is surjective. -/
theorem surjective_app_of_exactAt_cechComplex_one_of_lift
    {S : ShortComplex (Sheaf J AddCommGrpCat.{max w v})} (hS : S.ShortExact) {V : C}
    [HasFiniteProducts (Over V)]
    (hV : ∀ s : S.X₃.obj.obj (op V), ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ a, ∃ t : S.X₂.obj.obj (op (U a).left),
        S.g.hom.app _ t = S.X₃.obj.map (U a).hom.op s) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V ∧
      ((cechComplex U).obj S.X₁.obj).ExactAt 1) :
    Function.Surjective (S.g.hom.app (op V)) := fun s ↦ by
  obtain ⟨n, U, hlift, hcov, hU⟩ := hV s
  exact exists_app_g_eq_of_exactAt_cechComplex_one hS s U hlift hcov hU

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{max w v})] {T : C} (hT : IsTerminal T)
  [∀ V : C, HasFiniteProducts (Over V)]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max w v})]

include hT in
/-- **The Čech criterion for the vanishing of cohomology, with a lifting hypothesis.** Let `B` be
a class of objects of the site containing a terminal object `T`, and `Good` a class of finite
families generating covering sieves, whose Čech nerves lie in `B`. Assume that for every
epimorphism `G ⟶ H` of abelian sheaves, every section of `H` over a member `V` of `B` lifts to
`G` after restriction to the members of some family in `Good` over `V`. If the Čech complexes of
the abelian sheaf `F` on all families in `Good` (over members of `B`) are exact in positive
degrees, then `H^q(F) = 0` for `q > 0`. -/
theorem subsingleton_H_succ_of_exactAt_cechComplex_of_lift (B : C → Prop) (hBT : B T)
    (Good : ∀ V : C, ∀ n : ℕ, (Fin n → Over V) → Prop)
    (hGood : ∀ V n (U : Fin n → Over V), Good V n U →
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    (hlift : ∀ V, B V → ∀ {G H : Sheaf J AddCommGrpCat.{max w v}} (g : G ⟶ H) [Epi g]
      (s : H.obj.obj (op V)), ∃ (n : ℕ) (U : Fin n → Over V), Good V n U ∧
        ∀ a, ∃ t : G.obj.obj (op (U a).left), g.hom.app _ t = H.obj.map (U a).hom.op s)
    (F : Sheaf J AddCommGrpCat.{max w v})
    (hF : ∀ V, B V → ∀ n (U : Fin n → Over V), Good V n U →
      ∀ q : ℕ, ((cechComplex U).obj F.obj).ExactAt (q + 1))
    (q : ℕ) : Subsingleton (Sheaf.H F (q + 1)) := by
  -- for a short exact sequence `0 → F → I → Q → 0`, sections of `Q` over members of `B` lift
  have hsurj (F : Sheaf J AddCommGrpCat.{max w v})
      (hF : ∀ V, B V → ∀ n (U : Fin n → Over V), Good V n U →
        ∀ q : ℕ, ((cechComplex U).obj F.obj).ExactAt (q + 1))
      {S : ShortComplex (Sheaf J AddCommGrpCat.{max w v})} (hS : S.ShortExact) (hSF : S.X₁ = F)
      (V : C) (hV : B V) : Function.Surjective (S.g.hom.app (op V)) := by
    subst hSF
    have := hS.epi_g
    refine surjective_app_of_exactAt_cechComplex_one_of_lift hS fun s ↦ ?_
    obtain ⟨n, U, hU, ht⟩ := hlift V hV S.g s
    exact ⟨n, U, ht, (hGood V n U hU).2, hF V hV n U hU 0⟩
  induction q generalizing F with
  | zero =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    exact subsingleton_H_succ_of_comp_extClass hS 0
      (comp_extClass_eq_zero_of_surjective hT hS (hsurj F hF hS rfl T hBT))
  | succ q ih =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have := ih S.X₃ fun V hV n U hU q ↦ exactAt_cechComplex_of_sectionwise U S.f.hom S.g.hom
      app_g_app_f (injective_app_f hS) (exists_app_f_eq hS)
      (fun k y ↦ hsurj F hF hS rfl _ ((hGood V n U hU).1 k y)) q (hF V hV n U hU (q + 1))
      (exactAt_cechComplex_of_injective S.X₂ U q)
    exact subsingleton_H_succ_of_comp_extClass hS (q + 1) fun y ↦ by
      rw [Subsingleton.elim y 0, Ext.zero_comp]

end Sheaf

end CategoryTheory
