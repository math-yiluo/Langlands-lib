/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Lattice

/-! # Pulling back directed unions of subobjects

Source: the AB5 argument in Stacks Project, Tag 079A. The categorical proof first
handles monomorphisms using directed-intersection distributivity, and epimorphisms
using their cokernel universal property.
-/

@[expose] public section

universe w v u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {X Y : C} {ι : Type w} [Nonempty ι]

private lemma iSup_pullback_eq_top_mono (f : X ⟶ Y) [Mono f]
    (S : ι → Subobject Y) (hS : Directed (· ≤ ·) S)
    (h : Subobject.mk f ≤ ⨆ i, S i) :
    (⨆ i, (Subobject.pullback f).obj (S i)) = ⊤ := by
  apply Subobject.map_obj_injective f
  rw [← Subobject.exists_iso_map f, Subobject.exists_obj_iSup, Subobject.exists_obj_top]
  have hmap (i : ι) : (Subobject.map f).obj ((Subobject.pullback f).obj (S i)) =
      Subobject.mk f ⊓ S i :=
    (Subobject.inf_eq_map_pullback' (MonoOver.mk f) (S i)).symm
  simp only [Subobject.exists_iso_map f, hmap]
  rw [← inf_iSup_of_directed _ S hS, inf_eq_left.mpr h, imageSubobject_mono]

private lemma iSup_pullback_eq_top_epi (f : X ⟶ Y) [Epi f]
    (S : ι → Subobject Y) (h : (⨆ i, S i) = ⊤) :
    (⨆ i, (Subobject.pullback f).obj (S i)) = ⊤ := by
  let U := ⨆ i, (Subobject.pullback f).obj (S i)
  have him : imageSubobject (U.arrow ≫ f) = ⊤ := by
    rw [← Subobject.exists_obj_eq_imageSubobject, Subobject.exists_obj_iSup]
    simpa only [Subobject.exists_obj_pullback_obj] using h
  have hc : kernel.ι f ≫ cokernel.π U.arrow = 0 := by
    let i : ι := Classical.choice inferInstance
    have hk : ((Subobject.pullback f).obj (S i)).Factors (kernel.ι f) := by
      apply (pullback_factors_iff _ _ _).2
      simpa using (Subobject.factors_zero (P := S i) (X := kernel f))
    have hU := Subobject.factors_of_le _ (le_iSup (fun i ↦
      (Subobject.pullback f).obj (S i)) i) hk
    rw [← Subobject.factorThru_arrow _ _ hU, Category.assoc, cokernel.condition, comp_zero]
  let d := Abelian.epiDesc f (cokernel.π U.arrow) hc
  have hd : f ≫ d = cokernel.π U.arrow := Abelian.comp_epiDesc _ _ _
  have himd : (imageSubobject (U.arrow ≫ f)).arrow ≫ d = 0 := by
    apply imageSubobject_arrow_comp_eq_zero
    rw [Category.assoc, hd, cokernel.condition]
  have : Epi (imageSubobject (U.arrow ≫ f)).arrow := by
    rw [him]
    infer_instance
  have hd0 : d = 0 := by
    apply (cancel_epi (imageSubobject (U.arrow ≫ f)).arrow).1
    simpa using himd
  have : Epi U.arrow := Abelian.epi_of_cokernel_π_eq_zero _ (by rw [← hd, hd0, comp_zero])
  simpa only [Subobject.mk_arrow] using
    (Subobject.epi_iff_mk_eq_top U.arrow).1 inferInstance

/-- Pulling back a directed union along a map that factors through that union gives
a family with union the whole source. Source: Stacks Project, Tag 079A, AB5.
(auxiliary; not a blueprint node). -/
theorem iSup_pullback_eq_top_of_factors (f : X ⟶ Y)
    (S : ι → Subobject Y) (hS : Directed (· ≤ ·) S)
    (h : (⨆ i, S i).Factors f) :
    (⨆ i, (Subobject.pullback f).obj (S i)) = ⊤ := by
  have hi : Subobject.mk (image.ι f) ≤ ⨆ i, S i :=
    (Subobject.imageSubobject_le_iff _ _).2 h
  have hmono := iSup_pullback_eq_top_mono (image.ι f) S hS hi
  have hepi := iSup_pullback_eq_top_epi (factorThruImage f)
    (fun i ↦ (Subobject.pullback (image.ι f)).obj (S i)) hmono
  simpa only [← Subobject.pullback_comp, image.fac] using hepi

end CategoryTheory.IsGrothendieckAbelian
