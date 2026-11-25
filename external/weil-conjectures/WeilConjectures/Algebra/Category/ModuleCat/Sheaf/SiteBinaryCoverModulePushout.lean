/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteNestedExtensionMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing

/-! # The counit square of a binary covering is a pushout

Source: Stacks Project, Modules on Sites, Tags 03DI and 03EM and the sheaf gluing condition.
(blueprint: lem-dla1-site-binary-cover-module-pushout)
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

set_option autoImplicit false

universe c v r

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

open SubterminalLocal

private theorem nested_counit
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max c v r}) {A B : C} (a : A ⟶ B)
    (F : Modules.{c, v, r} R) :
    nested.{c, v, r} R a F ≫ (adj.{c, v, r} R B).counit.app F =
      (adj.{c, v, r} R A).counit.app F := by
  apply ((adj.{c, v, r} R A).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  rw [show ((adj.{c, v, r} R A).homEquiv _ _) (nested.{c, v, r} R a F) = _ from
    Equiv.apply_symm_apply _ _]
  rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components]
  let α := overFunctorMap.{max c v r} (coefficients.{c, v, r} R) a
  change (α.inv.app F ≫
    (overMap.{max c v r} (coefficients.{c, v, r} R) a).map
      ((adj.{c, v, r} R B).unit.app ((jstar.{c, v, r} R B).obj F)) ≫
    α.hom.app ((jbang.{c, v, r} R B).obj ((jstar.{c, v, r} R B).obj F))) ≫
    (jstar.{c, v, r} R A).map ((adj.{c, v, r} R B).counit.app F) = 𝟙 _
  rw [Category.assoc, Category.assoc, ← α.hom.naturality]
  simp only [CategoryTheory.Functor.comp_map]
  rw [← CategoryTheory.Functor.map_comp_assoc, Adjunction.right_triangle_components,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact α.inv_hom_id_app F

private theorem nested_homEquiv
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max c v r}) {A B : C} (a : A ⟶ B)
    (F G : Modules.{c, v, r} R)
    (f : (jbang.{c, v, r} R B).obj ((jstar.{c, v, r} R B).obj F) ⟶ G) :
    ((adj.{c, v, r} R A).homEquiv _ _) (nested.{c, v, r} R a F ≫ f) =
      (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) a).inv.app F ≫
        (overMap.{max c v r} (coefficients.{c, v, r} R) a).map
          (((adj.{c, v, r} R B).homEquiv _ _) f) ≫
        (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) a).hom.app G := by
  rw [Adjunction.homEquiv_naturality_right]
  simp only [nested, Equiv.apply_symm_apply, Adjunction.homEquiv_unit,
    CategoryTheory.Functor.map_comp]
  rw [Category.assoc, Category.assoc, ← NatTrans.naturality]
  simp only [CategoryTheory.Functor.comp_map, Category.assoc]

private theorem binary_hom_gluing
    {C : Type c} [Category.{v} C] (K : Precoverage C) [HasPullbacks C]
    (R : Sheaf K.toGrothendieck CommRingCat.{max c v r})
    {X U V : C} (hX : IsTerminal X) (u : U ⟶ X) (v : V ⟶ X) [Mono u] [Mono v]
    (hcover : Presieve.singleton u ⊔ Presieve.singleton v ∈ K X)
    (F G : Modules.{c, v, r} R)
    (α : (jstar.{c, v, r} R U).obj F ⟶ (jstar.{c, v, r} R U).obj G)
    (β : (jstar.{c, v, r} R V).obj F ⟶ (jstar.{c, v, r} R V).obj G)
    (hab : ∀ (T : C) (a : T ⟶ U) (b : T ⟶ V),
      α.val.app (op (Over.mk a)) = β.val.app (op (Over.mk b))) :
    ∃! f : F ⟶ G, (jstar.{c, v, r} R U).map f = α ∧
      (jstar.{c, v, r} R V).map f = β := by
  classical
  let Y : Bool → C := fun b ↦ if b then U else V
  let q : ∀ b, Y b ⟶ X := fun b ↦ match b with | true => u | false => v
  let φ : ∀ b, F.over (Y b) ⟶ G.over (Y b) :=
    fun b ↦ match b with | true => α | false => β
  have hp : Presieve.ofArrows Y q = Presieve.singleton u ⊔ Presieve.singleton v := by
    funext T f
    apply propext
    constructor
    · intro h
      obtain ⟨b⟩ := h
      cases b
      · exact Or.inr (Presieve.singleton_self v)
      · exact Or.inl (Presieve.singleton_self u)
    · intro h
      rcases h with h | h
      · cases h
        exact Presieve.ofArrows.mk true
      · cases h
        exact Presieve.ofArrows.mk false
  have hq : Sieve.ofArrows Y q ∈ K.toGrothendieck X := by
    change Sieve.generate (Presieve.ofArrows Y q) ∈ K.toGrothendieck X
    rw [hp]
    exact K.generate_mem_toGrothendieck hcover
  have hc : ∀ (i j : Bool) (T : C) (a : T ⟶ Limits.pullback (q i) (q j)),
      (φ i).val.app (op (Over.mk (a ≫ pullback.fst (q i) (q j)))) =
        (φ j).val.app (op (Over.mk (a ≫ pullback.snd (q i) (q j)))) := by
    intro i j T a
    cases i <;> cases j
    · have he : pullback.fst v v = pullback.snd v v :=
        (cancel_mono v).1 (pullback.condition (f := v) (g := v))
      simp only [φ, q]
      rw [he]
    · exact (hab T (a ≫ pullback.snd v u) (a ≫ pullback.fst v u)).symm
    · exact hab T (a ≫ pullback.fst u v) (a ≫ pullback.snd u v)
    · have he : pullback.fst u u = pullback.snd u u :=
        (cancel_mono u).1 (pullback.condition (f := u) (g := u))
      simp only [φ, q]
      rw [he]
  obtain ⟨fX, hfX, huniq⟩ := existsUnique_hom_of_cover
    R.obj (coefficients.{c, v, r} R).property F G X Bool Y q hq φ hc
  let f : F ⟶ G :=
    { val :=
      { app := fun T ↦ fX.val.app (op (Over.mk (hX.from T.unop)))
        naturality := by
          intro T S k
          let l : Over.mk (hX.from S.unop) ⟶ Over.mk (hX.from T.unop) :=
            Over.homMk k.unop (hX.hom_ext _ _)
          exact fX.val.naturality l.op } }
  have hfU : (jstar.{c, v, r} R U).map f = α := by
    ext T x
    obtain ⟨T⟩ := T
    have h := hfX true T.left T.hom
    have he : hX.from T.left = T.hom ≫ u := hX.hom_ext _ _
    change fX.val.app (op (Over.mk (hX.from T.left))) x = α.val.app (op T) x
    rw [he]
    exact congrArg (fun k ↦ k x) h
  have hfV : (jstar.{c, v, r} R V).map f = β := by
    ext T x
    obtain ⟨T⟩ := T
    have h := hfX false T.left T.hom
    have he : hX.from T.left = T.hom ≫ v := hX.hom_ext _ _
    change fX.val.app (op (Over.mk (hX.from T.left))) x = β.val.app (op T) x
    rw [he]
    exact congrArg (fun k ↦ k x) h
  refine ⟨f, ⟨hfU, hfV⟩, ?_⟩
  intro g hg
  have he : (jstar.{c, v, r} R X).map g = fX := huniq _ (by
    intro i T a
    cases i
    · exact congrArg (fun k ↦ k.val.app (op (Over.mk a))) hg.2
    · exact congrArg (fun k ↦ k.val.app (op (Over.mk a))) hg.1)
  ext T x
  exact congrArg (fun k ↦ k.val.app (op (Over.mk (hX.from T.unop))) x) he

/-- The overlap and the two counits give the pushout associated to a binary covering.
Source: Stacks Project, Modules on Sites, Tags 03DI and 03EM; Sites, the sheaf gluing condition
(blueprint: lem-dla1-site-binary-cover-module-pushout).

Proof: the two paths around the square agree by transposing with the overlap
adjunction and using its triangle identities and the restriction comparison.
Fix any target module G. By the normalized extension/restriction adjunction,
maps from the U and V terms to G are respectively maps F|U → G|U and
F|V → G|V. Transpose once more on the overlap. The definition of nested as
the transpose of the restriction of the unit, and naturality of the slice
comparison, identify agreement after the two nested maps with agreement of
these two module maps on the intersection slice. Such compatible maps glue
uniquely to F → G. Explicitly, over an arbitrary T, pull the covering of X
back along the terminal map T → X. Apply the two maps to restrictions of a
section of F on the two covering members. On their fibre products the images
agree by the overlap condition, so the sheaf condition for G glues them
uniquely. Separatedness shows that this assignment commutes with restriction
and is additive and O-linear, by checking these equations on that cover.
The same separatedness proves uniqueness of the resulting module map.
The adjunction identifies its two composites with the original maps.
This is exactly the universal property of the displayed pushout. -/
theorem siteBinaryCoverModulePushout
    {C : Type c} [Category.{v} C] (K : Precoverage C)
    (_hsite : K.IsSiteForCoverings) [HasPullbacks C]
    (R : Sheaf K.toGrothendieck CommRingCat.{max c v r})
    {X U V : C} (hX : IsTerminal X) (u : U ⟶ X) (v : V ⟶ X) [Mono u] [Mono v]
    (hcover : Presieve.singleton u ⊔ Presieve.singleton v ∈ K X)
    (F : Modules.{c, v, r} R) :
    IsPushout (nested.{c, v, r} R (Limits.pullback.fst u v) F)
      (nested.{c, v, r} R (Limits.pullback.snd u v) F)
      ((adj.{c, v, r} R U).counit.app F) ((adj.{c, v, r} R V).counit.app F) := by
  classical
  have hw : nested.{c, v, r} R (pullback.fst u v) F ≫
        (adj.{c, v, r} R U).counit.app F =
      nested.{c, v, r} R (pullback.snd u v) F ≫
        (adj.{c, v, r} R V).counit.app F := by
    rw [nested_counit.{c, v, r}, nested_counit.{c, v, r}]
  have hd (G : Modules.{c, v, r} R)
      (a : (jbang.{c, v, r} R U).obj ((jstar.{c, v, r} R U).obj F) ⟶ G)
      (b : (jbang.{c, v, r} R V).obj ((jstar.{c, v, r} R V).obj F) ⟶ G)
      (hab : nested.{c, v, r} R (pullback.fst u v) F ≫ a =
        nested.{c, v, r} R (pullback.snd u v) F ≫ b) :
      ∃! f : F ⟶ G, (adj.{c, v, r} R U).counit.app F ≫ f = a ∧
        (adj.{c, v, r} R V).counit.app F ≫ f = b := by
    let a' := ((adj.{c, v, r} R U).homEquiv _ _) a
    let b' := ((adj.{c, v, r} R V).homEquiv _ _) b
    have hcompat (T : C) (p : T ⟶ U) (q : T ⟶ V) :
        a'.val.app (op (Over.mk p)) = b'.val.app (op (Over.mk q)) := by
      let t : T ⟶ Limits.pullback u v := pullback.lift p q (hX.hom_ext _ _)
      have h := congrArg ((adj.{c, v, r} R (Limits.pullback u v)).homEquiv _ _) hab
      rw [nested_homEquiv.{c, v, r}, nested_homEquiv.{c, v, r}] at h
      have hh := congrArg (fun k ↦ k.val.app (op (Over.mk t))) h
      change a'.val.app (op (Over.mk (t ≫ pullback.fst u v))) =
        b'.val.app (op (Over.mk (t ≫ pullback.snd u v))) at hh
      dsimp only [t] at hh
      rw [pullback.lift_fst, pullback.lift_snd] at hh
      exact hh
    obtain ⟨f, hf, huniq⟩ := binary_hom_gluing.{c, v, r} K R hX u v hcover F G a' b'
      hcompat
    have htranspose (Z : C) (g : F ⟶ G) :
        ((adj.{c, v, r} R Z).homEquiv _ _)
          ((adj.{c, v, r} R Z).counit.app F ≫ g) =
            (jstar.{c, v, r} R Z).map g := by
      rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit,
        Adjunction.right_triangle_components, Category.id_comp]
    refine ⟨f, ⟨?_, ?_⟩, ?_⟩
    · apply ((adj.{c, v, r} R U).homEquiv _ _).injective
      rw [htranspose]
      exact hf.1
    · apply ((adj.{c, v, r} R V).homEquiv _ _).injective
      rw [htranspose]
      exact hf.2
    · intro g hg
      apply huniq g
      constructor
      · rw [← htranspose, hg.1]
      · rw [← htranspose, hg.2]
  let d (s : PushoutCocone (nested.{c, v, r} R (pullback.fst u v) F)
      (nested.{c, v, r} R (pullback.snd u v) F)) :=
    (hd s.pt s.inl s.inr s.condition).exists.choose
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hw)
  apply PushoutCocone.IsColimit.mk hw d
  · intro s
    exact (hd s.pt s.inl s.inr s.condition).exists.choose_spec.1
  · intro s
    exact (hd s.pt s.inl s.inr s.condition).exists.choose_spec.2
  · intro s m hm hn
    exact (hd s.pt s.inl s.inr s.condition).unique ⟨hm, hn⟩
      (hd s.pt s.inl s.inr s.condition).exists.choose_spec

end SheafOfModules
