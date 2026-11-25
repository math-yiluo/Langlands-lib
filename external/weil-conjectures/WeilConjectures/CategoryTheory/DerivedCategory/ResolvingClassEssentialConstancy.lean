/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-! # Resolving classes give essentially constant denominator diagrams

Source: Stacks Project, Tag 06XN, dual proof, and Tag 05PU(2).
(blueprint: lem-pur-resolving-class-essential-constancy).
-/

@[expose] public section

universe u v uH vH

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A resolving class gives a denominator cone with the retraction/factorization
criterion of essential constancy. At an object of the class its identity leg is invertible.
Source: Stacks Project, Tag 06XN (dual proof), and Categories, Tag 05PU(2).
(blueprint: lem-pur-resolving-class-essential-constancy).

Proof: The right fraction calculus makes `W.Over ⊤ X` cofiltered. Resolve the source of
any denominator to obtain a denominator whose source lies in `P`. These form an initial
full subcategory: common refinements and equalizations in the denominator category can
again be resolved. Two-out-of-three makes every transition between such resolutions a
member of `W`, hence its image under `F` is invertible. Choose a resolution `j₀`. For any
`j`, choose a common resolution `k` mapping to `j₀` and `j`, and define the leg to `j` as
`inv (F.map (k ⟶ j₀)) ≫ F.map (k ⟶ j)`. Common refinements and equalizations show
independence of this choice and naturality. The leg at `j₀` is the identity, so take
`r = 𝟙 _`; the chosen common refinements give the factorization criterion. If `X ∈ P`,
include its identity denominator in the initial subcategory; the leg there is a composite
of invertible transition maps and is therefore invertible. -/
theorem resolvingClass_essentialConstancy
    {C : Type u} [Category.{v} C] {H : Type uH} [Category.{vH} H]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    [W.HasTwoOutOfThreeProperty] (F : C ⥤ H) (P : Set C)
    (hres : ∀ X : C, ∃ (X' : C) (s : X' ⟶ X), X' ∈ P ∧ W s)
    (hinv : ∀ (X X' : C) (s : X ⟶ X'),
      X ∈ P → X' ∈ P → W s → IsIso (F.map s)) (X : C) :
    let G := MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F
    ∃ (Y : H) (u : (Functor.const (W.Over ⊤ X)).obj Y ⟶ G),
      IsEssentiallyConstantProDiagram G Y ∧
        (∃ (j₀ : W.Over ⊤ X) (r : G.obj j₀ ⟶ Y),
          u.app j₀ ≫ r = 𝟙 Y ∧
            ∀ j : W.Over ⊤ X, ∃ (k : W.Over ⊤ X) (a : k ⟶ j₀) (b : k ⟶ j),
              G.map b = G.map a ≫ r ≫ u.app j) ∧
        ∀ h : W (𝟙 X), X ∈ P →
          IsIso (u.app (⟨Over.mk (𝟙 X), h⟩ : W.Over ⊤ X)) := by
  classical
  dsimp only
  let J := W.Over ⊤ X
  let G := MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F
  have hj : IsCofiltered J := by
    refine {
      nonempty := ⟨MorphismProperty.Over.mk (P := W) ⊤ (𝟙 X) (W.id_mem X)⟩
      cone_objs := ?_
      cone_maps := ?_ }
    · intro j j'
      obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk j.hom j'.hom j'.prop).exists_rightFraction
      let k : J := MorphismProperty.Over.mk (P := W) ⊤ (ψ.s ≫ j.hom) (W.comp_mem _ _ ψ.hs j.prop)
      exact ⟨k, MorphismProperty.Over.homMk ψ.s, MorphismProperty.Over.homMk ψ.f hψ.symm, trivial⟩
    · intro j j' f g
      obtain ⟨Z, t, ht, heq⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
        f.left g.left j'.hom j'.prop (f.w.trans g.w.symm)
      let k : J := MorphismProperty.Over.mk (P := W) ⊤ (t ≫ j.hom) (W.comp_mem _ _ ht j.prop)
      refine ⟨k, MorphismProperty.Over.homMk t, ?_⟩
      exact MorphismProperty.Over.Hom.ext heq
  let : IsCofiltered J := hj
  let R : ObjectProperty J := fun j ↦ j.left ∈ P
  let i := R.ι
  have hresolve : ∀ j : J, ∃ r : R.FullSubcategory, Nonempty (i.obj r ⟶ j) := by
    intro j
    obtain ⟨Z, s, hZ, hs⟩ := hres j.left
    let k : J := MorphismProperty.Over.mk (P := W) ⊤ (s ≫ j.hom) (W.comp_mem _ _ hs j.prop)
    exact ⟨⟨k, hZ⟩, ⟨MorphismProperty.Over.homMk s⟩⟩
  have : i.Initial := i.initial_of_exists_of_isCofiltered_of_fullyFaithful hresolve
  have hr : IsCofiltered R.FullSubcategory := by
    obtain ⟨r, _⟩ := hresolve (MorphismProperty.Over.mk (P := W) ⊤ (𝟙 X) (W.id_mem X))
    exact {
      __ := IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful i hresolve
      nonempty := ⟨r⟩ }
  let : IsCofiltered R.FullSubcategory := hr
  have hmaps : ∀ {r r' : R.FullSubcategory} (f : r ⟶ r'),
      IsIso ((i ⋙ G).map f) := by
    intro r r' f
    apply hinv _ _ f.hom.left r.property r'.property
    exact W.of_postcomp f.hom.left r'.obj.hom r'.obj.prop
      (by rw [MorphismProperty.Over.w f.hom]; exact r.obj.prop)
  let r₀ : R.FullSubcategory := hr.nonempty.some
  have hevent : (i ⋙ G).IsEventuallyConstantTo r₀ := fun _ f ↦ hmaps f
  let c := hevent.cone
  let u := (Functor.Initial.extendCone (F := i) (G := G)).obj c
  have hu₀ : u.π.app (i.obj r₀) = 𝟙 (G.obj (i.obj r₀)) := by
    rw [Functor.Initial.extendCone_obj_π_app' (F := i) c (𝟙 (i.obj r₀))]
    simp [c, Functor.IsEventuallyConstantTo.cone]
  have hcriterion : ∃ (j₀ : J) (r : G.obj j₀ ⟶ u.pt),
      u.π.app j₀ ≫ r = 𝟙 u.pt ∧
        ∀ j : J, ∃ (k : J) (a : k ⟶ j₀) (b : k ⟶ j),
          G.map b = G.map a ≫ r ≫ u.π.app j := by
    refine ⟨i.obj r₀, 𝟙 _, ?_, ?_⟩
    · change u.π.app (i.obj r₀) ≫ 𝟙 _ = 𝟙 (G.obj (i.obj r₀))
      simpa only [Category.comp_id] using hu₀
    · intro j
      let k := IsCofiltered.min (i.obj r₀) j
      let a := IsCofiltered.minToLeft (i.obj r₀) j
      let b := IsCofiltered.minToRight (i.obj r₀) j
      obtain ⟨r, ⟨s⟩⟩ := hresolve k
      have hiso : IsIso (G.map (s ≫ a)) := by
        exact hmaps (ObjectProperty.homMk (s ≫ a))
      have hnat₀ := u.w (s ≫ a)
      rw [hu₀] at hnat₀
      have hnat₀' : u.π.app (i.obj r) = CategoryTheory.inv (G.map (s ≫ a)) := by
        apply (cancel_mono (G.map (s ≫ a))).1
        change u.π.app (i.obj r) ≫ G.map (s ≫ a) =
          CategoryTheory.inv (G.map (s ≫ a)) ≫ G.map (s ≫ a)
        rw [IsIso.inv_hom_id]
        exact hnat₀
      have hnat := u.w (s ≫ b)
      rw [hnat₀'] at hnat
      refine ⟨i.obj r, s ≫ a, s ≫ b, ?_⟩
      rw [← hnat]
      simp
  refine ⟨u.pt, u.π, ⟨hj, ?_⟩, hcriterion, ?_⟩
  · obtain ⟨j₀, r, hret, hfac⟩ := hcriterion
    exact ⟨u.π, j₀, r, hret, hfac⟩
  · intro h hX
    let r : R.FullSubcategory := ⟨⟨Over.mk (𝟙 X), h⟩, hX⟩
    have hevent' : (i ⋙ G).IsEventuallyConstantTo r := fun _ f ↦ hmaps f
    have hc := hevent.isLimitCone
    have hiso : IsIso (c.π.app r) := hevent'.isIso_π_of_isLimit hc
    have hid : u.π.app (i.obj r) = c.π.app r := by
      rw [Functor.Initial.extendCone_obj_π_app' (F := i) c (𝟙 (i.obj r))]
      simp
    change IsIso (u.π.app (i.obj r))
    rw [hid]
    exact hiso

end CategoryTheory.Functor
