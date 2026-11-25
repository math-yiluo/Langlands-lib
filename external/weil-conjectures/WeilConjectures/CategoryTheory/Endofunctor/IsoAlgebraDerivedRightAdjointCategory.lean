/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Data.Int.Init
public import WeilConjectures.CategoryTheory.WeilEquivariance

/-!
# Categorical lemmas for lifting right adjoints to algebras

This file collects general categorical facts used to lift the right adjoint of a right derived
functor to the derived categories of algebras with invertible structure morphism
(`WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjoint`).

- `CategoryTheory.Limits.isIso_of_cofan_inj_comp_eq`: a morphism between coproducts that maps
  each summand isomorphically onto the corresponding summand is an isomorphism, and
  `CategoryTheory.Limits.isColimitCofanMkOfIso`: colimit cofans are invariant under isomorphisms.
- `CategoryTheory.exists_iso_summand_comp_eq`: an equivariant morphism between objects with
  `ℤ`-indexed families of summands defined recursively via an endofunctor maps every summand
  isomorphically onto the corresponding summand as soon as it does so for the summand `0`.
- `CategoryTheory.Adjunction.isIso_rightAdjointExchange_app`: the right adjoint exchange of
  an isomorphism `L ⋙ β ≅ α ⋙ L` for an adjunction `L ⊣ R` is an isomorphism if `α` is an
  equivalence and `β` is fully faithful.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

namespace Limits

/-- A morphism between the points of two coproduct cofans which maps each summand
isomorphically onto the corresponding summand is an isomorphism. -/
lemma isIso_of_cofan_inj_comp_eq {C : Type*} [Category* C] {J : Type*} {P Q : J → C}
    {c : Cofan P} {d : Cofan Q} (hc : IsColimit c) (hd : IsColimit d) (φ : c.pt ⟶ d.pt)
    (t : ∀ j, P j ≅ Q j) (h : ∀ j, c.inj j ≫ φ = (t j).hom ≫ d.inj j) : IsIso φ := by
  refine ⟨Cofan.IsColimit.desc hd (fun j ↦ (t j).inv ≫ c.inj j), ?_, ?_⟩
  · refine Cofan.IsColimit.hom_ext hc _ _ fun j ↦ ?_
    rw [reassoc_of% (h j), Cofan.IsColimit.fac, Iso.hom_inv_id_assoc, Category.comp_id]
  · refine Cofan.IsColimit.hom_ext hd _ _ fun j ↦ ?_
    rw [Cofan.IsColimit.fac_assoc, Category.assoc, h, Iso.inv_hom_id_assoc, Category.comp_id]

/-- A cofan isomorphic, summand by summand and on the point, to a colimit cofan is a colimit
cofan. -/
noncomputable def isColimitCofanMkOfIso {C : Type*} [Category* C] {J : Type*} {P P' : J → C}
    {X X' : C} {p : ∀ j, P j ⟶ X} {p' : ∀ j, P' j ⟶ X'} (h : IsColimit (Cofan.mk X p))
    (a : ∀ j, P' j ≅ P j) (b : X' ≅ X) (w : ∀ j, p' j ≫ b.hom = (a j).hom ≫ p j) :
    IsColimit (Cofan.mk X' p') :=
  have hf {Y : C} (f : ∀ j, P j ⟶ Y) (j : J) : p j ≫ Cofan.IsColimit.desc h f = f j :=
    Cofan.IsColimit.fac h f j
  Cofan.IsColimit.mk _ (fun t ↦ b.hom ≫ Cofan.IsColimit.desc h (fun j ↦ (a j).inv ≫ t.inj j))
    (fun t j ↦ by
      dsimp
      rw [reassoc_of% (w j), hf, Iso.hom_inv_id_assoc])
    (fun t m hm ↦ by
      rw [← Iso.inv_comp_eq]
      refine Cofan.IsColimit.hom_ext h _ _ fun j ↦ ?_
      have hj : p j ≫ b.inv = (a j).inv ≫ p' j := by
        rw [Iso.comp_inv_eq, Category.assoc, w, Iso.inv_hom_id_assoc]
      dsimp at hm ⊢
      rw [reassoc_of% hj, hm, hf])

end Limits

/-- Let `Γ` be a fully faithful endofunctor, and let `φ : P ⟶ Q` be a morphism compatible with
morphisms `sP : Γ P ⟶ P` and `sQ : Γ Q ⟶ Q`, `sQ` being an isomorphism. Let `pₙ : Pₙ ⟶ P` and
`qₙ : Qₙ ⟶ Q` (`n : ℤ`) be families of morphisms with `pₙ₊₁ = ρₙ ≫ Γ pₙ ≫ sP` and
`qₙ₊₁ = μₙ ≫ Γ qₙ ≫ sQ` for isomorphisms `ρₙ : Pₙ₊₁ ≅ Γ Pₙ` and `μₙ : Qₙ₊₁ ≅ Γ Qₙ`. If
`p₀ ≫ φ = t₀ ≫ q₀` for an isomorphism `t₀`, then for every `n` there is an isomorphism
`tₙ : Pₙ ≅ Qₙ` with `pₙ ≫ φ = tₙ ≫ qₙ`. -/
lemma exists_iso_summand_comp_eq {C : Type*} [Category* C] (Γ : C ⥤ C) [Γ.Full] [Γ.Faithful]
    {P Q : C} {Pn Qn : ℤ → C} (p : ∀ n, Pn n ⟶ P) (q : ∀ n, Qn n ⟶ Q)
    (sP : Γ.obj P ⟶ P) (sQ : Γ.obj Q ⟶ Q) [IsIso sQ]
    (ρ : ∀ n, Pn (n + 1) ≅ Γ.obj (Pn n)) (μ : ∀ n, Qn (n + 1) ≅ Γ.obj (Qn n))
    (hp : ∀ n, p (n + 1) = (ρ n).hom ≫ Γ.map (p n) ≫ sP)
    (hq : ∀ n, q (n + 1) = (μ n).hom ≫ Γ.map (q n) ≫ sQ)
    (φ : P ⟶ Q) (hφ : Γ.map φ ≫ sQ = sP ≫ φ)
    (t₀ : Pn 0 ≅ Qn 0) (h₀ : p 0 ≫ φ = t₀.hom ≫ q 0) (n : ℤ) :
    ∃ t : Pn n ≅ Qn n, p n ≫ φ = t.hom ≫ q n := by
  have up (m : ℤ) (h : ∃ t : Pn m ≅ Qn m, p m ≫ φ = t.hom ≫ q m) :
      ∃ t : Pn (m + 1) ≅ Qn (m + 1), p (m + 1) ≫ φ = t.hom ≫ q (m + 1) := by
    obtain ⟨t, ht⟩ := h
    refine ⟨ρ m ≪≫ Γ.mapIso t ≪≫ (μ m).symm, ?_⟩
    rw [hp, hq, Category.assoc, Category.assoc, ← hφ, ← Γ.map_comp_assoc, ht]
    simp
  have down (m : ℤ) (h : ∃ t : Pn (m + 1) ≅ Qn (m + 1), p (m + 1) ≫ φ = t.hom ≫ q (m + 1)) :
      ∃ t : Pn m ≅ Qn m, p m ≫ φ = t.hom ≫ q m := by
    obtain ⟨t, ht⟩ := h
    refine ⟨Γ.preimageIso ((ρ m).symm ≪≫ t ≪≫ μ m), Γ.map_injective ?_⟩
    rw [← cancel_mono sQ, Γ.map_comp, Category.assoc, hφ, Γ.map_comp, Functor.preimageIso_hom,
      Functor.map_preimage]
    have hp' := hp m
    rw [← Iso.inv_comp_eq] at hp'
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← reassoc_of% hp', ht, hq m]
  induction n using Int.induction_on with
  | zero => exact ⟨t₀, h₀⟩
  | succ i ih => exact up _ ih
  | pred i ih =>
    have hi : -(i : ℤ) - 1 + 1 = -i := by omega
    exact down _ (by rw [hi]; exact ih)

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {α : C ⥤ C} {β : D ⥤ D} (e : L ⋙ β ≅ α ⋙ L)

/-- The right adjoint exchange `R ⋙ α ⟶ β ⋙ R` of an isomorphism `e : L ⋙ β ≅ α ⋙ L` for an
adjunction `L ⊣ R` is an isomorphism if `α` is an equivalence and `β` is fully faithful.
```
   D ---R---> C
   |          |
   β    ⟹    α
   v          v
   D ---R---> C
```
-/
lemma isIso_rightAdjointExchange_app [α.IsEquivalence] [β.Full] [β.Faithful] (d : D) :
    IsIso ((rightAdjointExchange adj adj e).app d) := by
  have hc : L.map ((rightAdjointExchange adj adj e).app d) ≫ adj.counit.app (β.obj d) =
      e.inv.app (R.obj d) ≫ β.map (adj.counit.app d) := by
    rw [← hom_app_comp_map_rightAdjointExchange_app_comp_counit adj adj e d,
      Iso.inv_hom_id_app_assoc]
  -- the transpose of `x ≫ exchange`
  have htr (T : C) (x : T ⟶ α.obj (R.obj d)) :
      (adj.homEquiv _ _).symm (x ≫ (rightAdjointExchange adj adj e).app d) =
        L.map x ≫ e.inv.app (R.obj d) ≫ β.map (adj.counit.app d) := by
    rw [homEquiv_counit, L.map_comp, Category.assoc, hc]
  apply isIso_of_yoneda_map_bijective
  intro T
  let T' := α.objPreimage T
  let i : α.obj T' ≅ T := α.objObjPreimageIso T
  -- every morphism `T ⟶ α (R d)` is `i⁻¹ ≫ α g` for a unique `g`
  have hx (x : T ⟶ α.obj (R.obj d)) : x = i.inv ≫ α.map (α.preimage (i.hom ≫ x)) := by
    simp
  have key (g : T' ⟶ R.obj d) :
      (adj.homEquiv _ _).symm ((i.inv ≫ α.map g) ≫ (rightAdjointExchange adj adj e).app d) =
        L.map i.inv ≫ e.inv.app T' ≫ β.map ((adj.homEquiv _ _).symm g) := by
    rw [htr, homEquiv_counit, L.map_comp, Category.assoc, β.map_comp]
    congr 1
    have := e.inv.naturality g
    dsimp at this
    rw [reassoc_of% this]
  constructor
  · intro x x' hxx
    have h := congrArg (adj.homEquiv _ _).symm hxx
    dsimp only at h
    rw [hx x, hx x', key, key, cancel_epi, cancel_epi] at h
    rw [hx x, hx x', (adj.homEquiv _ _).symm.injective (β.map_injective h)]
  · intro y
    let z : β.obj (L.obj T') ⟶ β.obj d :=
      e.hom.app T' ≫ L.map i.hom ≫ (adj.homEquiv _ _).symm y
    refine ⟨i.inv ≫ α.map (adj.homEquiv _ _ (β.preimage z)), ?_⟩
    apply (adj.homEquiv _ _).symm.injective
    dsimp only
    rw [key, Equiv.symm_apply_apply, Functor.map_preimage]
    simp [z, ← L.map_comp_assoc]

end Adjunction

end CategoryTheory
