/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.EventuallyAffine

/-!
# Affineness descends to a finite stage

Source: Stacks Project, Limits, Lemma 01ZN in Situation 081D
(blueprint: lem-weil-pbc-descend-affine).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private def upperTailEquivalence {I : Type u} [Preorder I] (i₀ : I) :
    (Set.Ici i₀)ᵒᵖ ≌ Over (op i₀) where
  functor :=
    { obj := fun i ↦ Over.mk (homOfLE i.unop.property).op
      map := fun f ↦ Over.homMk (homOfLE (leOfHom f.unop)).op
      map_id := by intros; ext; apply Subsingleton.elim
      map_comp := by intros; ext; apply Subsingleton.elim }
  inverse :=
    { obj := fun i ↦ op ⟨i.left.unop, leOfHom i.hom.unop⟩
      map := fun f ↦ (homOfLE (leOfHom f.left.unop)).op
      map_id := by intros; apply Subsingleton.elim
      map_comp := by intros; apply Subsingleton.elim }
  unitIso := NatIso.ofComponents (fun i ↦ Iso.refl i)
  counitIso := NatIso.ofComponents
    (fun i ↦ Over.isoMk (Iso.refl i.left))

/-- Source: Stacks Project, Limits, Lemma 01ZN in Situation 081D
(blueprint: lem-weil-pbc-descend-affine).
An affine base change to the inverse limit is affine at some stage above the chosen index.
The structure morphism of `X₀` is `f₀ ≫ h`, so `f₀` is a morphism over the chosen base.

Proof:
1. The transition maps and limit projections are affine
   (lem-weil-pbc-limit-affine-transition). Their base changes are affine
   (lem-weil-pbc-affine-morphism-permanence). Cartesian-square pasting identifies the
   induced map with the base change of f₀ (lem-weil-pbc-cartesian-square-pasting).
   Since X₀ and Y₀ are qcqs, these maps are qcqs
   (lem-weil-pbc-qcqs-morphism-permanence).
2. Choose a finite affine open cover Vⱼ,₀ of Y₀ (def-pc-scheme and
   definition-ind-etale-pro-etale-weakly--3). Its preimages Vⱼ,T cover each base-changed target
   and are affine. Put Uⱼ,T = f_T⁻¹(Vⱼ,T). They are qcqs by
   lem-weil-pbc-open-preimage-fibre-product and lem-weil-pbc-qcqs-over-affine.
3. At the limit, Uⱼ is affine since f is affine (pqf-def-affine-morphism).
4. Each Uⱼ is the limit of Uⱼ,i over the upper tail, with affine transitions
   (lem-weil-pbc-scheme-over-limit and lem-weil-pbc-limit-cone-affine-projections-opens).
5. Each Uⱼ,i is affine for all sufficiently large i (lem-weil-pbc-limit-affine-stage).
6. Directedness gives a common index for the finitely many j. At that index all the
   preimages of the affine cover are affine, so f_i is affine
   (pqf-lem-affine-local-target). For the empty cover take the chosen index itself. -/
theorem exists_isAffineHom_baseChange_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    {X₀ Y₀ : Scheme.{u}} [CompactSpace X₀] [QuasiSeparatedSpace X₀]
    [CompactSpace Y₀] [QuasiSeparatedSpace Y₀]
    (f₀ : X₀ ⟶ Y₀) (h : Y₀ ⟶ D.obj (op i₀))
    (hf : IsAffineHom
      (pullback.map (f₀ ≫ h) (c.π.app (op i₀)) h (c.π.app (op i₀))
        f₀ (𝟙 c.pt) (𝟙 (D.obj (op i₀)))
        (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm))) :
    ∃ (i : I) (hi : i₀ ≤ i), IsAffineHom
      (pullback.map (f₀ ≫ h) (D.map (homOfLE hi).op) h (D.map (homOfLE hi).op)
        f₀ (𝟙 (D.obj (op i))) (𝟙 (D.obj (op i₀)))
        (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) := by
  -- Descend the composite Xᵢ → Y₀ using the fixed-target affine-limit theorem.
  -- The affine projection Yᵢ → Y₀ then cancels from this composite.
  let : Nonempty I := ⟨i₀⟩
  let : Nonempty (Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirected (Set.Ici i₀) (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨k, ha, hb⟩ := IsDirected.directed (r := (· ≤ ·)) a.val b.val
    exact ⟨⟨k, a.property.trans ha⟩, ha, hb⟩⟩
  let F := (upperTailEquivalence i₀).functor
  let E := F ⋙ baseChangeDiagram D (f₀ ≫ h)
  have : ∀ j, CompactSpace (E.obj j) := fun j ↦
    baseChangeDiagram_compactSpace (D := D) (f₀ ≫ h) (F.obj j)
  have : ∀ j, QuasiSeparatedSpace (E.obj j) := fun j ↦
    baseChangeDiagram_quasiSeparatedSpace (D := D) (f₀ ≫ h) (F.obj j)
  have : ∀ {j k} (a : j ⟶ k), IsAffineHom (E.map a) := fun a ↦ by
    change IsAffineHom ((baseChangeDiagram D (f₀ ≫ h)).map (F.map a))
    infer_instance
  let t := (baseChangeCone D c (f₀ ≫ h)).whisker F
  have ht : IsLimit t :=
    (Functor.Initial.isLimitWhiskerEquiv F _).symm
      (isLimitBaseChangeCone D c (f₀ ≫ h) hc)
  let g : E ⟶ (Functor.const (Set.Ici i₀)ᵒᵖ).obj Y₀ :=
    { app := fun j ↦ pullback.fst _ _ ≫ f₀
      naturality := by
        intro j k a
        simp [E] }
  let m := pullback.map (f₀ ≫ h) (c.π.app (op i₀)) h (c.π.app (op i₀))
    f₀ (𝟙 c.pt) (𝟙 (D.obj (op i₀)))
    (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)
  have : IsAffineHom (c.π.app (op i₀)) := isAffineHom_π_app D c hc _
  have : IsAffineHom (pullback.fst h (c.π.app (op i₀))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : IsAffineHom m := hf
  have hm : m ≫ pullback.fst h (c.π.app (op i₀)) =
      pullback.fst (f₀ ≫ h) (c.π.app (op i₀)) ≫ f₀ := by simp [m]
  have : IsAffineHom (pullback.fst (f₀ ≫ h) (c.π.app (op i₀)) ≫ f₀) := by
    rw [← hm]
    infer_instance
  obtain ⟨j, hj⟩ := eventually_affine Y₀ E g t ht
    (pullback.fst (f₀ ≫ h) (c.π.app (op i₀)) ≫ f₀) (by
      intro j
      simp [t, g, E])
  refine ⟨j.val, j.property, ?_⟩
  have H := hj j le_rfl
  change IsAffineHom
    (pullback.fst (f₀ ≫ h) (D.map (homOfLE j.property).op) ≫ f₀) at H
  have : IsAffineHom (pullback.fst h (D.map (homOfLE j.property).op)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  apply (IsAffineHom.comp_iff
    (g := pullback.fst h (D.map (homOfLE j.property).op))).mp
  simpa using H

end AlgebraicGeometry
