/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.CategoryTheory.Filtered.Basic

import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Basic.Finite.Prod

/-!
# The finite-presieve sheaf condition and filtered colimits

Source: Stacks Project, Categories, Tag 002W; Sites, Tag 00VM.
-/

@[expose] public section

universe v u₁ w t

open CategoryTheory.Limits CategoryTheory.ConcreteCategory Opposite

namespace CategoryTheory

private theorem finite_sections_lift
    {C : Type u₁} [Category.{v} C]
    {Λ : Type t} [SmallCategory Λ] [IsFiltered Λ] [UnivLE.{t, w}]
    (D : Λ ⥤ Cᵒᵖ ⥤ Type w) (c : Cocone D) (hc : IsColimit c)
    {I : Type*} [Finite I] (Y : I → C) (x : ∀ i, c.pt.obj (op (Y i))) :
    ∃ (k : Λ) (y : ∀ i, (D.obj k).obj (op (Y i))),
      ∀ i, (c.ι.app k).app (op (Y i)) (y i) = x i := by
  classical
  have : Fintype I := Fintype.ofFinite I
  have hs (i : I) := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj (op (Y i))) hc) (x i)
  choose j y hy using hs
  obtain ⟨s⟩ := IsFiltered.cocone_nonempty (Discrete.functor j)
  refine ⟨s.pt, fun i ↦ (D.map (s.ι.app ⟨i⟩)).app _ (y i), fun i ↦ ?_⟩
  have hw := congrArg (fun t ↦ t.app (op (Y i))) (c.w (s.ι.app ⟨i⟩))
  exact (congr_hom hw (y i)).trans (hy i)

private theorem finite_sections_equal
    {C : Type u₁} [Category.{v} C]
    {Λ : Type t} [SmallCategory Λ] [IsFiltered Λ] [UnivLE.{t, w}]
    (D : Λ ⥤ Cᵒᵖ ⥤ Type w) (c : Cocone D) (hc : IsColimit c)
    {I : Type*} [Finite I] (Y : I → C) (j : Λ)
    (x y : ∀ i, (D.obj j).obj (op (Y i)))
    (h : ∀ i, (c.ι.app j).app _ (x i) = (c.ι.app j).app _ (y i)) :
    ∃ (k : Λ) (f : j ⟶ k), ∀ i,
      (D.map f).app (op (Y i)) (x i) = (D.map f).app (op (Y i)) (y i) := by
  classical
  have hs (i : I) := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves ((evaluation _ _).obj (op (Y i))) hc) (x i) (y i)).mp (h i)
  choose k f hf using hs
  obtain ⟨l, g, q, hq⟩ := IsFiltered.wideSpan f
  refine ⟨l, g, fun i ↦ ?_⟩
  rw [← hq i]
  simp only [Functor.map_comp, NatTrans.comp_app, types_comp_apply]
  exact congrArg ((D.map (q i)).app _) (hf i)

/-- A filtered colimit of presheaves satisfying the sheaf condition for one finite
presieve with pairwise pullbacks satisfies that same condition.
Source: Stacks Project, Sites, Tag 0738(4) and Tag 00VM; Categories, Tag 002W
(blueprint: lem-weil-pbc-finite-presieve-filtered-colimit).

Proof: Index the arrows of R by its finite subtype of uncurried arrows. Evaluation
preserves presheaf colimits. For separatedness, lift two sections over X to a common
stage. Their restrictions agree in the colimit over each arrow of R, so each such
equality holds after a transition. The finite wide-span lemma for filtered categories
makes all of these transitions factor through a single transition. Separatedness at
that stage identifies the two sections, hence their images in the colimit agree.

For existence, lift the finitely many members of a compatible family to stages of
the diagram, and take a cocone over the finite discrete diagram of those stages.
This gives a family at one stage. For each pair of arrows of R, compatibility of its
image implies equality of the two restrictions over the pairwise pullback after a
transition. There are finitely many pairs, so the finite wide-span lemma again gives
one transition making every compatibility equation hold. At that stage the sheaf
condition provides an amalgamation. Its image amalgamates the original family by
naturality and the cocone equations. Empty R causes no exception: the finite discrete
cocone and the wide-span construction also apply to empty index sets, and the
stagewise empty-presieve sheaf condition supplies the unique section over X.

This is the finite-stage argument of Sites Tag 0738(4), applied directly to the
sectionwise presheaf colimit and the sheaf condition of Tag 00VM. -/
theorem finitePresieve_isSheafFor_filteredColimit
    {C : Type u₁} [Category.{v} C]
    {Λ : Type t} [SmallCategory Λ] [IsFiltered Λ] [UnivLE.{t, w}]
    (D : Λ ⥤ Cᵒᵖ ⥤ Type w) (c : Cocone D) (hc : IsColimit c)
    {X : C} (R : Presieve X) [R.HasPairwisePullbacks]
    (hfinite : R.uncurry.Finite)
    (hD : ∀ i, R.IsSheafFor (D.obj i)) : R.IsSheafFor c.pt := by
  classical
  let I := R.uncurry
  have : Finite I := Set.finite_coe_iff.mpr hfinite
  let Y : I → C := fun i ↦ i.val.1
  let f : ∀ i : I, Y i ⟶ X := fun i ↦ i.val.2
  have hf (i : I) : R (f i) := i.property
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  have hsep : R.IsSeparatedFor c.pt := by
    intro z a b haz hbz
    have hab {Z : C} {h : Z ⟶ X} (hh : R h) :
        c.pt.map h.op a = c.pt.map h.op b := (haz h hh).trans (hbz h hh).symm
    obtain ⟨j, a', b', ha, hb⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (isColimitOfPreserves ((evaluation _ _).obj (op X)) hc) a b
    change (c.ι.app j).app (op X) a' = a at ha
    change (c.ι.app j).app (op X) b' = b at hb
    have heq (i : I) :
        (c.ι.app j).app (op (Y i)) ((D.obj j).map (f i).op a') =
        (c.ι.app j).app (op (Y i)) ((D.obj j).map (f i).op b') := by
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ha, hb]
      exact hab (hf i)
    obtain ⟨k, g, hg⟩ := finite_sections_equal D c hc Y j
      (fun i ↦ (D.obj j).map (f i).op a')
      (fun i ↦ (D.obj j).map (f i).op b') heq
    have he : (D.map g).app (op X) a' = (D.map g).app (op X) b' := by
      apply (hD k).isSeparatedFor.ext
      intro Z h hh
      have eq := hg (⟨⟨Z, h⟩, hh⟩ : I)
      simpa only [Y, f, NatTrans.naturality_apply] using eq
    have hw := congrArg (fun t ↦ t.app (op X)) (c.w g)
    calc
      a = (c.ι.app j).app (op X) a' := ha.symm
      _ = (c.ι.app k).app (op X) ((D.map g).app (op X) a') :=
        (congr_hom hw a').symm
      _ = (c.ι.app k).app (op X) ((D.map g).app (op X) b') := congrArg _ he
      _ = (c.ι.app j).app (op X) b' := congr_hom hw b'
      _ = b := hb
  refine ⟨hsep, ?_⟩
  intro x hx
  obtain ⟨j, y, hy⟩ := finite_sections_lift D c hc Y (fun i ↦ x (f i) (hf i))
  have hp (ij : I × I) : HasPullback (f ij.1) (f ij.2) :=
    Presieve.HasPairwisePullbacks.has_pullbacks (hf ij.1) (hf ij.2)
  let Z : I × I → C := fun ij ↦ @pullback _ _ _ _ _ (f ij.1) (f ij.2) (hp ij)
  let a : ∀ ij : I × I, (D.obj j).obj (op (Z ij)) := fun ij ↦
    have := hp ij
    (D.obj j).map (pullback.fst (f ij.1) (f ij.2)).op (y ij.1)
  let b : ∀ ij : I × I, (D.obj j).obj (op (Z ij)) := fun ij ↦
    have := hp ij
    (D.obj j).map (pullback.snd (f ij.1) (f ij.2)).op (y ij.2)
  have heq (ij : I × I) :
      (c.ι.app j).app (op (Z ij)) (a ij) = (c.ι.app j).app (op (Z ij)) (b ij) := by
    have := hp ij
    dsimp [a, b, Z]
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    exact (congrArg (c.pt.map (pullback.fst (f ij.1) (f ij.2)).op) (hy ij.1)).trans
      (((Presieve.pullbackCompatible_iff x).mp hx (hf ij.1) (hf ij.2)).trans
        (congrArg (c.pt.map (pullback.snd (f ij.1) (f ij.2)).op) (hy ij.2)).symm)
  obtain ⟨k, g, hg⟩ := finite_sections_equal D c hc Z j a b heq
  let z : R.FamilyOfElements (D.obj k) := fun T h hh ↦
    (D.map g).app (op T) (y (⟨⟨T, h⟩, hh⟩ : I))
  have hz : z.Compatible := by
    rw [Presieve.pullbackCompatible_iff]
    intro T₁ T₂ h₁ h₂ hh₁ hh₂
    let i₁ : I := ⟨⟨T₁, h₁⟩, hh₁⟩
    let i₂ : I := ⟨⟨T₂, h₂⟩, hh₂⟩
    have := hp (i₁, i₂)
    have eq := hg (i₁, i₂)
    simpa only [a, b, z, Z, i₁, i₂, Y, f, NatTrans.naturality_apply] using eq
  obtain ⟨s, hs, _⟩ := hD k z hz
  refine ⟨(c.ι.app k).app (op X) s, ?_⟩
  intro T h hh
  let i : I := ⟨⟨T, h⟩, hh⟩
  have hw := congrArg (fun t ↦ t.app (op T)) (c.w g)
  calc
    c.pt.map h.op ((c.ι.app k).app (op X) s) =
        (c.ι.app k).app (op T) ((D.obj k).map h.op s) :=
      (NatTrans.naturality_apply (c.ι.app k) h.op s).symm
    _ = (c.ι.app k).app (op T) ((D.map g).app (op T) (y i)) :=
      congrArg _ (hs h hh)
    _ = (c.ι.app j).app (op T) (y i) := congr_hom hw (y i)
    _ = x h hh := hy i

end CategoryTheory
