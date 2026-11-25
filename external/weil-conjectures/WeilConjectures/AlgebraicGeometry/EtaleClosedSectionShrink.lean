/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Shrinking one local étale representative along a closed subscheme

Source: Stacks Project, Tag 09ZF, fourth proof paragraph, open-image shrinking.
(blueprint: lem-weil-pbc-etale-closed-section-shrink).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A local representative can be shrunk so its unit equation holds everywhere on
its closed base change. Source: Stacks Project, Tag 09ZF, fourth proof paragraph.
(blueprint: lem-weil-pbc-etale-closed-section-shrink).

Proof: The morphism a is étale, hence has open image O in U times_X Z.
The projection of this fibre product to U is a closed embedding. Therefore O
is the inverse image of an ambient open U' of U. Restrict s to U'. The map a
factors through U' times_X Z, and is surjective onto it by the choice of U'.
This is a one-member étale cover. Restrict ht to this factorization; unit
naturality identifies its right side with the restriction of i⁻¹(s|U').
The sheaf separatedness axiom gives equality on U' times_X Z. The terminal
map in ht is the unique map into the base change of the identity object,
so it is the composite of a with the base-changed structure map of U.
Every point in W maps into U', giving the range inclusion. For W empty,
choose U' empty, and use the empty-cover sheaf axiom. No global covering,
compactness, or Zariski-unit injectivity assumption enters this assertion. -/
theorem etale_closed_section_shrink
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk (𝟙 X)))))
    (W : Z.Etale) (U : X.Etale)
    (a : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ i).obj U)
    (s : F.obj.obj (op U))
    (ht : ((Scheme.etaleSetPullback i).obj F).obj.map
        (((MorphismProperty.Over.mkIdTerminal @Etale X).isTerminalObj
          (MorphismProperty.Over.pullback @Etale ⊤ i) (Scheme.Etale.mk (𝟙 X))).from W).op
        t = ((Scheme.etaleSetPullback i).obj F).obj.map a.op
          (etaleSetDescentUnit i F U s)) :
    ∃ (U' : X.Etale) (s' : F.obj.obj (op U')),
      Set.range (W.hom ≫ i) ⊆ Set.range U'.hom ∧
      etaleSetDescentUnit i F U' s' =
        ((Scheme.etaleSetPullback i).obj F).obj.map
          ((MorphismProperty.Over.pullback @Etale ⊤ i).map
            (MorphismProperty.Over.homMk U'.hom (Category.comp_id _) :
              U' ⟶ Scheme.Etale.mk (𝟙 X))).op t := by
  classical
  let B := MorphismProperty.Over.pullback @Etale ⊤ i
  let H := (Scheme.etaleSetPullback i).obj F
  let p : (B.obj U).left ⟶ U.left := pullback.fst U.hom i
  have hp : IsClosedImmersion p := inferInstance
  have ha : Etale a.left := inferInstance
  obtain ⟨O, hO, hpre⟩ := p.isClosedEmbedding.isInducing.isOpen_iff.mp
    a.left.isOpenMap.isOpen_range
  let L : U.left.Opens := ⟨O, hO⟩
  have hU : Etale U.hom := U.prop
  let U' : X.Etale := Scheme.Etale.mk (L.ι ≫ U.hom)
  let b : U' ⟶ U := MorphismProperty.Over.homMk L.ι rfl
  have hr : Set.range (a.left ≫ p) ⊆ Set.range L.ι := by
    rintro x ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change p (a.left y) ∈ O
    have hy : a.left y ∈ Set.range a.left := ⟨y, rfl⟩
    rw [← hpre] at hy
    exact hy
  let l : W.left ⟶ U'.left := IsOpenImmersion.lift L.ι (a.left ≫ p) hr
  have hl : l ≫ L.ι = a.left ≫ p := IsOpenImmersion.lift_fac _ _ _
  have hw : l ≫ U'.hom = W.hom ≫ i := by
    change l ≫ L.ι ≫ U.hom = W.hom ≫ i
    rw [← Category.assoc, hl, Category.assoc]
    change a.left ≫ pullback.fst U.hom i ≫ U.hom = _
    rw [pullback.condition, ← Category.assoc]
    have h := MorphismProperty.Over.w a
    exact congrArg (fun k ↦ k ≫ i) h
  let a' : W ⟶ B.obj U' := MorphismProperty.Over.homMk
    (pullback.lift l W.hom hw) (pullback.lift_snd _ _ _)
  have hab : a' ≫ B.map b = a := by
    apply (Scheme.Etale.forget Z ⋙ Over.forget Z).map_injective
    change pullback.lift l W.hom hw ≫ pullback.map _ _ _ _ L.ι (𝟙 Z) (𝟙 X)
      (by simp [U']) (by simp) = a.left
    apply pullback.hom_ext
    · simpa [p] using hl
    · simpa using (MorphismProperty.Over.w a).symm
  have hclosed : IsOpenImmersion (B.map b).left := by
    change IsOpenImmersion (pullback.map _ _ _ _ L.ι (𝟙 Z) (𝟙 X)
      (by simp [U']) (by simp))
    infer_instance
  have hsurj : Surjective a'.left := ⟨by
    intro x
    have hx : (B.map b).left x ∈ Set.range a.left := by
      rw [← hpre]
      have hfst : (B.map b).left ≫ p = pullback.fst U'.hom i ≫ L.ι := by
        change pullback.map _ _ _ _ L.ι (𝟙 Z) (𝟙 X)
          (by simp [U']) (by simp) ≫
          pullback.fst U.hom i = _
        simp
      change p ((B.map b).left x) ∈ O
      rw [← Scheme.Hom.comp_apply, hfst, Scheme.Hom.comp_apply]
      exact (pullback.fst U'.hom i x).property
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    apply (B.map b).left.isOpenEmbedding.injective
    have hh := congrArg (fun k ↦ k.left y) hab
    change (B.map b).left (a'.left y) = a.left y at hh
    exact hh.trans hy⟩
  let s' : F.obj.obj (op U') := F.obj.map b.op s
  refine ⟨U', s', ?_, ?_⟩
  · rintro x ⟨y, rfl⟩
    refine ⟨l y, ?_⟩
    exact congrArg (fun k ↦ k y) hw
  · have hc : Sieve.ofArrows (fun _ : PUnit.{1} ↦ W) (fun _ ↦ a') ∈
        Z.smallEtaleTopology (B.obj U') := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
      simp only [Set.iUnion_const]
      exact Set.range_eq_univ.mpr a'.left.surjective
    have heq :
        TypeCat.ofHom (fun _ : PUnit.{u + 2} ↦ etaleSetDescentUnit i F U' s') =
        TypeCat.ofHom (fun _ : PUnit.{u + 2} ↦ H.obj.map
          (B.map (MorphismProperty.Over.homMk U'.hom (Category.comp_id _) :
            U' ⟶ Scheme.Etale.mk (𝟙 X))).op t) := by
      apply H.property.hom_ext_ofArrows (fun _ : PUnit.{1} ↦ a') hc
      intro j
      ext v
      change H.obj.map a'.op (etaleSetDescentUnit i F U' s') =
        H.obj.map a'.op (H.obj.map
          (B.map (MorphismProperty.Over.homMk U'.hom (Category.comp_id _) :
            U' ⟶ Scheme.Etale.mk (𝟙 X))).op t)
      have hn := etaleSetInverseImageCompositionUnits.1 X Z i F U U' b s
      change etaleSetDescentUnit i F U' s' =
        H.obj.map (B.map b).op (etaleSetDescentUnit i F U s) at hn
      rw [hn, ← Functor.map_comp_apply, ← op_comp, hab,
        ← Functor.map_comp_apply, ← op_comp]
      have hterm : a' ≫ B.map
          (MorphismProperty.Over.homMk U'.hom (Category.comp_id _) :
            U' ⟶ Scheme.Etale.mk (𝟙 X)) =
          ((MorphismProperty.Over.mkIdTerminal @Etale X).isTerminalObj B _).from W :=
        ((MorphismProperty.Over.mkIdTerminal @Etale X).isTerminalObj B _).hom_ext _ _
      rw [hterm]
      exact ht.symm
    exact ConcreteCategory.congr_hom heq PUnit.unit

end AlgebraicGeometry
