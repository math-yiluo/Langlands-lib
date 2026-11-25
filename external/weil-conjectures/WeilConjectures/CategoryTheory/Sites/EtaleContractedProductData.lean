/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.CategoryTheory.Sites.SheafifyAddAction
import WeilConjectures.CategoryTheory.Sites.SheafifySimplyTransitive

/-! # The explicit orbit presheaf for coefficient change of torsors

Source: Stacks Project, Tags 03AH and 03AJ; contracted-product quotient construction.
(blueprint: lem-sc-etale-contracted-product-exists-data).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


namespace CategoryTheory.Sheaf.Torsor

variable (S : Scheme.{u})
    {G G' : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : G ⟶ G') (T : Torsor G)

/-- The generators of the antidiagonal orbit relation. 
(blueprint: lem-sc-etale-contracted-product-exists-data)
-/
def contractedOrbitRel (U : S.Etaleᵒᵖ)
    (a b : T.sheaf.obj.obj U × G'.obj.obj U) : Prop :=
  ∃ g : G.obj.obj U, b = (T.vadd U g a.1, a.2 - φ.hom.app U g)

/-- Sectionwise orbits, with restriction induced from the two factors. 
(blueprint: lem-sc-etale-contracted-product-exists-data)
-/
def contractedOrbitPresheaf : S.Etaleᵒᵖ ⥤ Type (u + 1) where
  obj U := Quot (contractedOrbitRel S φ T U)
  map {U V} f := ↾(Quot.lift
    (fun (a : T.sheaf.obj.obj U × G'.obj.obj U) ↦ Quot.mk (contractedOrbitRel S φ T V)
      (T.sheaf.obj.map f a.1, G'.obj.map f a.2)) (by
        intro a b hab
        obtain ⟨g, rfl⟩ := hab
        apply Quot.sound
        refine ⟨G.obj.map f g, ?_⟩
        simp only [T.map_vadd, map_sub]
        congr 1
        have h := ConcreteCategory.congr_hom (φ.hom.naturality f) g
        exact congrArg (fun z ↦ G'.obj.map f a.2 - z) h.symm) )
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro x
    induction x using Quot.ind with
    | mk a =>
      change Quot.mk _ (T.sheaf.obj.map (𝟙 U) a.1, G'.obj.map (𝟙 U) a.2) = _
      simp only [Functor.map_id]
      rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    induction x using Quot.ind with
    | mk a =>
      change Quot.mk _ (T.sheaf.obj.map (f ≫ g) a.1, G'.obj.map (f ≫ g) a.2) =
        Quot.mk _ (T.sheaf.obj.map g (T.sheaf.obj.map f a.1),
          G'.obj.map g (G'.obj.map f a.2))
      simp only [Functor.map_comp]
      rfl

/-- The actual sheafification of the orbit presheaf; no witness is chosen. 
(blueprint: lem-sc-etale-contracted-product-exists-data)
-/
noncomputable def contractedOrbitSheaf : Sheaf S.smallEtaleTopology (Type (u + 1)) :=
  (presheafToSheaf S.smallEtaleTopology (Type (u + 1))).obj
    (contractedOrbitPresheaf S φ T)

/-- The canonical map from pairs to the sheafified orbit presheaf. 
(blueprint: lem-sc-etale-contracted-product-exists-data)
-/
noncomputable def contractedOrbitQuotient (U : S.Etaleᵒᵖ)
    (t : T.sheaf.obj.obj U) (h : G'.obj.obj U) :
    (contractedOrbitSheaf S φ T).obj.obj U :=
  (toSheafify S.smallEtaleTopology (contractedOrbitPresheaf S φ T)).app U
    (Quot.mk _ (t, h))

/-- (blueprint: lem-sc-etale-contracted-product-exists-data) -/
lemma contractedOrbitQuotient_natural {U V : S.Etaleᵒᵖ} (f : U ⟶ V)
    (t : T.sheaf.obj.obj U) (h : G'.obj.obj U) :
    (contractedOrbitSheaf S φ T).obj.map f (contractedOrbitQuotient S φ T U t h) =
      contractedOrbitQuotient S φ T V (T.sheaf.obj.map f t) (G'.obj.map f h) := by
  exact (ConcreteCategory.congr_hom ((toSheafify S.smallEtaleTopology
    (contractedOrbitPresheaf S φ T)).naturality f) (Quot.mk _ (t, h))).symm

/-- (blueprint: lem-sc-etale-contracted-product-exists-data) -/
lemma contractedOrbitQuotient_invariant (U : S.Etaleᵒᵖ) (g : G.obj.obj U)
    (t : T.sheaf.obj.obj U) (h : G'.obj.obj U) :
    contractedOrbitQuotient S φ T U (T.vadd U g t) (h - φ.hom.app U g) =
      contractedOrbitQuotient S φ T U t h := by
  apply congrArg ((toSheafify S.smallEtaleTopology
    (contractedOrbitPresheaf S φ T)).app U)
  exact (Quot.sound ⟨g, rfl⟩).symm

/-- Local nonemptiness passes from the original torsor to its orbit sheaf. 
(blueprint: lem-sc-etale-contracted-product-exists-data)
-/
lemma contractedOrbitSheaf_nonemptySieve_mem (U : S.Etale) :
    nonemptySieve (contractedOrbitSheaf S φ T).obj U ∈ S.smallEtaleTopology U := by
  apply S.smallEtaleTopology.superset_covering _ (T.nonemptySieve_mem U)
  intro V f hf
  obtain ⟨t⟩ := hf
  exact ⟨contractedOrbitQuotient S φ T (Opposite.op V) t 0⟩

/-- A section trivializes the sectionwise orbit quotient, with the expected second coordinate.
This is the explicit local coordinate used in the local torsor argument. 
(blueprint: lem-sc-etale-contracted-product-exists-data)
-/
noncomputable def contractedOrbitEquiv (U : S.Etaleᵒᵖ) (t₀ : T.sheaf.obj.obj U) :
    Quot (contractedOrbitRel S φ T U) ≃ G'.obj.obj U := by
  let e : G.obj.obj U ≃ T.sheaf.obj.obj U :=
    Equiv.ofBijective (T.vadd U · t₀) (T.bijective_vadd U t₀)
  have he (t : T.sheaf.obj.obj U) : T.vadd U (e.symm t) t₀ = t :=
    e.apply_symm_apply t
  have hg (g : G.obj.obj U) (t : T.sheaf.obj.obj U) :
      e.symm (T.vadd U g t) = g + e.symm t := by
    apply e.injective
    change T.vadd U (e.symm (T.vadd U g t)) t₀ = T.vadd U (g + e.symm t) t₀
    rw [he, T.add_vadd, he]
  have hzero : e.symm t₀ = 0 := by
    apply e.injective
    change T.vadd U (e.symm t₀) t₀ = T.vadd U 0 t₀
    rw [he, T.zero_vadd]
  refine
    { toFun := Quot.lift (fun a ↦ a.2 + φ.hom.app U (e.symm a.1)) ?_
      invFun := fun h ↦ Quot.mk _ (t₀, h)
      left_inv := ?_
      right_inv := ?_ }
  · intro a b hab
    obtain ⟨g, rfl⟩ := hab
    rw [hg, map_add]
    simp only [sub_eq_add_neg]
    abel
  · intro x
    induction x using Quot.ind with
    | mk a =>
      apply Quot.sound
      refine ⟨e.symm a.1, ?_⟩
      simp only [he]
      simp only [add_sub_cancel_right]
  · intro h
    change h + φ.hom.app U (e.symm t₀) = h
    rw [hzero, map_zero, add_zero]

/-- Translation on the sheafified orbit quotient makes it a torsor.
Source: Stacks Project, Tags 03AH and 03AJ; the local orbit-trivialization argument.
(blueprint: lem-sc-etale-contracted-product-exists-data)

Proof: On the orbit presheaf, addition of h in the second coordinate commutes with every
antidiagonal generator. It therefore defines an action morphism. Sheafification preserves
finite products; extend that morphism to the sheafification, identifying the sheafification
of the underlying group presheaf with G'. The action laws and restriction compatibility
follow from their presheaf versions by the sheafification universal property. On any object
where T has a section t0, simple transitivity identifies each orbit uniquely with (t0,h).
The same identification after sheafification is a local isomorphism with G'. These local
isomorphisms imply simple transitivity on arbitrary sections by sheaf gluing, and local
nonemptiness follows from the covering sieve of sections of T. Translation of the canonical
quotient map is the original second-coordinate translation. All arguments remain valid
for the zero group, zero coefficient morphism and empty scheme. For uniqueness, the quotient
translation equation determines the action on every local image q(t,h). Every section of Q
locally has such a representative, since the sheafification unit is locally surjective.
Naturality and sheaf separatedness therefore determine the action on every section. -/
theorem exists_contracted_product_action :
    ∃! vadd : ∀ U : S.Etaleᵒᵖ, G'.obj.obj U →
        (contractedOrbitSheaf S φ T).obj.obj U → (contractedOrbitSheaf S φ T).obj.obj U,
      (∀ U t, vadd U 0 t = t) ∧
      (∀ U g h t, vadd U (g + h) t = vadd U g (vadd U h t)) ∧
      (∀ ⦃U V⦄ (f : U ⟶ V) g t,
        (contractedOrbitSheaf S φ T).obj.map f (vadd U g t) =
          vadd V (G'.obj.map f g) ((contractedOrbitSheaf S φ T).obj.map f t)) ∧
      (∀ U t, Function.Bijective (vadd U · t)) ∧
      (∀ U t h k, contractedOrbitQuotient S φ T U t (h + k) =
        vadd U k (contractedOrbitQuotient S φ T U t h)) := by
  let P := contractedOrbitPresheaf S φ T
  let a : ∀ U, G'.obj.obj U → P.obj U → P.obj U := fun U k ↦
    Quot.lift (fun x ↦ Quot.mk (contractedOrbitRel S φ T U) (x.1, x.2 + k)) (by
      intro x y hxy
      obtain ⟨g, rfl⟩ := hxy
      apply Quot.sound
      refine ⟨g, ?_⟩
      congr 1
      dsimp
      abel)
  have az : ∀ U t, a U 0 t = t := by
    intro U t
    induction t using Quot.ind with
    | mk x => change Quot.mk _ (x.1, x.2 + 0) = Quot.mk _ x; simp
  have aa : ∀ U g h t, a U (g + h) t = a U g (a U h t) := by
    intro U g h t
    induction t using Quot.ind with
    | mk x =>
      change Quot.mk _ (x.1, x.2 + (g + h)) = Quot.mk _ (x.1, (x.2 + h) + g)
      congr 1
      abel_nf
  have an : ∀ ⦃U V⦄ (f : U ⟶ V) g t,
      P.map f (a U g t) = a V (G'.obj.map f g) (P.map f t) := by
    intro U V f g t
    induction t using Quot.ind with
    | mk x =>
      change Quot.mk _ (T.sheaf.obj.map f x.1, G'.obj.map f (x.2 + g)) =
        Quot.mk _ (T.sheaf.obj.map f x.1, G'.obj.map f x.2 + G'.obj.map f g)
      rw [map_add]
  have ab : ∀ U t, Function.Bijective (a U · t) := by
    intro U t
    induction t using Quot.ind with
    | mk x =>
      let e := contractedOrbitEquiv S φ T U x.1
      have he : ∀ k, e (a U k (Quot.mk _ x)) = x.2 + k := by
        intro k
        change (x.2 + k) + φ.hom.app U
          ((Equiv.ofBijective (T.vadd U · x.1) (T.bijective_vadd U x.1)).symm x.1) = _
        have hz : (Equiv.ofBijective (T.vadd U · x.1)
            (T.bijective_vadd U x.1)).symm x.1 = 0 := by
          apply (T.bijective_vadd U x.1).injective
          exact (Equiv.ofBijective (T.vadd U · x.1)
            (T.bijective_vadd U x.1)).apply_symm_apply x.1 |>.trans
              (T.zero_vadd U x.1).symm
        rw [hz, map_zero, add_zero]
      constructor
      · intro g h hgh
        have heq := congrArg e hgh
        rw [he, he] at heq
        exact add_left_cancel heq
      · intro y
        obtain ⟨k, hk⟩ := (Equiv.addLeft x.2).surjective (e y)
        refine ⟨k, e.injective ?_⟩
        rw [he]
        exact hk
  obtain ⟨b, ⟨bz, ba, bn, bq⟩, bu⟩ :=
    existsUnique_sheafify_add_action S.smallEtaleTopology G' P a az aa an
  have bb := bijective_sheafify_add_action S.smallEtaleTopology G' P a an ab b bn bq
  refine ⟨b, ⟨bz, ba, bn, bb, ?_⟩, ?_⟩
  · intro U t h k
    exact (bq U k (Quot.mk _ (t, h))).symm
  · intro c hc
    apply bu c
    refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
    intro U g t
    induction t using Quot.ind with
    | mk x => exact (hc.2.2.2.2 U x.1 x.2 g).symm


end CategoryTheory.Sheaf.Torsor

