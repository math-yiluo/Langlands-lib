/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits

import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-!
# Lifting a homology quotient through an epimorphism

Source: blueprint def-sp-convergence, cycle/boundary recursion; Stacks Section 12.20
(blueprint: lem-sp-subobject-homology-step).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem pullback_kernel {A B D : C} (f : A ⟶ B) (g : B ⟶ D) :
    (Subobject.pullback f).obj (kernelSubobject g) = kernelSubobject (f ≫ g) := by
  apply le_antisymm
  · apply le_kernelSubobject
    have hf := (Subobject.factors_pullback_obj_iff f (kernelSubobject g) _).mp
      ((Subobject.le_iff_factors_arrow _ _).mp le_rfl)
    simpa only [Category.assoc] using (kernelSubobject_factors_iff g _).mp hf
  · apply (Subobject.le_iff_factors_arrow _ _).mpr
    apply (Subobject.factors_pullback_obj_iff _ _ _).mpr
    apply kernelSubobject_factors
    simpa only [Category.assoc] using kernelSubobject_arrow_comp (f ≫ g)

/-- One local step of the cycle/boundary recursion, for a short complex and an epimorphic
presentation of its middle object. Pull back its kernel and image to `Z`, then embed them
in `T`, obtaining `Z'` and `B'`. The image of the incoming map lies in the outgoing kernel,
so `B' ≤ Z' ≤ Z`. The old kernel lies in the inverse image of every subobject, so `B ≤ B'`.
The pullback projection `Z' → kernel d` is uniquely specified by its composite with the
kernel inclusion; pullback stability of epimorphisms makes it epi. Composing with the
cokernel of `kernel.lift d b w` stays epi. The kernel of that composite is the inverse
image of `image b`: the kernel of the cokernel in an abelian category is the image of its
input, and inverse image commutes with kernel. Under the inclusion in `T`, that inverse
image is exactly `B'`, hence the displayed kernel-subobject identity.
This is a single local quotient step, with no grading, page recursion or infinite tower.
Source: blueprint def-sp-convergence, sentences defining the successor cycles, boundaries
and quotient; Stacks Section 12.20 (blueprint: lem-sp-subobject-homology-step). -/
theorem subobjectHomology_step {T E H F : C} (Z B : Subobject T) (hBZ : B ≤ Z)
    (π : (Z : C) ⟶ E) [Epi π]
    (hker : kernelSubobject π = Subobject.mk (Subobject.ofLE B Z hBZ))
    (b : H ⟶ E) (d : E ⟶ F) (w : b ≫ d = 0) :
    let Z' := (Subobject.«exists» Z.arrow).obj
      ((Subobject.pullback π).obj (kernelSubobject d))
    let B' := (Subobject.«exists» Z.arrow).obj
      ((Subobject.pullback π).obj (imageSubobject b))
    ∃ (hZ : Z' ≤ Z) (_hB : B ≤ B') (hBZ' : B' ≤ Z'),
      ∃ l : (Z' : C) ⟶ kernel d,
        l ≫ kernel.ι d = Subobject.ofLE Z' Z hZ ≫ π ∧
        Epi (l ≫ cokernel.π (kernel.lift d b w)) ∧
        kernelSubobject (l ≫ cokernel.π (kernel.lift d b w)) =
          Subobject.mk (Subobject.ofLE B' Z' hBZ') := by
  let P := (Subobject.pullback π).obj (kernelSubobject d)
  let Q := (Subobject.pullback π).obj (imageSubobject b)
  let Z' := (Subobject.«exists» Z.arrow).obj P
  let B' := (Subobject.«exists» Z.arrow).obj Q
  have hZe : Z' = Subobject.mk (P.arrow ≫ Z.arrow) := by
    dsimp [Z']
    rw [Subobject.exists_iso_map]
    exact Subobject.map_obj_eq_mk _ _
  have hZ : Z' ≤ Z := by
    rw [hZe]
    exact Subobject.mk_le_of_comm P.arrow rfl
  have hb : imageSubobject b ≤ kernelSubobject d :=
    (Subobject.imageSubobject_le_iff _ _).mpr (kernelSubobject_factors d b w)
  have hBZ' : B' ≤ Z' :=
    (Subobject.«exists» Z.arrow).monotone ((Subobject.pullback π).monotone hb)
  have hB : B ≤ B' := by
    have hkQ : kernelSubobject π ≤ Q := by
      apply (Subobject.le_iff_factors_arrow _ _).mpr
      apply (Subobject.factors_pullback_obj_iff _ _ _).mpr
      rw [kernelSubobject_arrow_comp]
      exact Subobject.factors_zero
    have he : (Subobject.«exists» Z.arrow).obj (kernelSubobject π) = B := by
      rw [hker, Subobject.exists_iso_map, Subobject.map_mk]
      simp
    rw [← he]
    exact (Subobject.«exists» Z.arrow).monotone hkQ
  let e := Subobject.isoOfEqMk Z' (P.arrow ≫ Z.arrow) hZe
  let l := e.hom ≫ Subobject.pullbackπ π (kernelSubobject d) ≫
    (kernelSubobjectIso d).hom
  have hj : e.hom ≫ P.arrow = Subobject.ofLE Z' Z hZ := by
    apply (cancel_mono Z.arrow).mp
    simp [e, Category.assoc]
  have hl : l ≫ kernel.ι d = Subobject.ofLE Z' Z hZ ≫ π := by
    dsimp [l]
    rw [Category.assoc, Category.assoc, kernelSubobject_arrow,
      (Subobject.isPullback π (kernelSubobject d)).w, ← Category.assoc, hj]
  have hep : Epi (Subobject.pullbackπ π (kernelSubobject d)) :=
    Abelian.epi_fst_of_isLimit _ _ (Subobject.isPullback π (kernelSubobject d)).isLimit
  let := hep
  have hel : Epi l := by dsimp [l]; infer_instance
  let := hel
  refine ⟨hZ, hB, hBZ', l, hl, inferInstance, ?_⟩
  let k := kernel.lift d b w
  let c := cokernel.π k
  have hquot : kernelSubobject c = imageSubobject k := by
    exact ((ShortComplex.mk k c (cokernel.condition k)).exact_iff_image_eq_kernel.mp
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel k))).symm
  have himage : (Subobject.map (kernel.ι d)).obj (kernelSubobject c) =
      imageSubobject b := by
    rw [hquot, ← Subobject.exists_iso_map, Subobject.exists_obj_eq_imageSubobject]
    rw [← imageSubobject_comp_of_epi (factorThruImageSubobject k)
      ((imageSubobject k).arrow ≫ kernel.ι d), ← Category.assoc,
      imageSubobject_arrow_comp]
    simp [k]
  have hmap : (Subobject.map Z'.arrow).obj
      (Subobject.mk (Subobject.ofLE B' Z' hBZ')) = B' := by
    rw [Subobject.map_mk]
    simp
  have hBpull : (Subobject.pullback Z'.arrow).obj B' =
      Subobject.mk (Subobject.ofLE B' Z' hBZ') := by
    conv_lhs => rw [← hmap, Subobject.pullback_map_self]
  change kernelSubobject (l ≫ c) = _
  calc
    kernelSubobject (l ≫ c) = (Subobject.pullback l).obj (kernelSubobject c) :=
      (pullback_kernel l c).symm
    _ = (Subobject.pullback (l ≫ kernel.ι d)).obj (imageSubobject b) := by
      rw [← himage, Subobject.pullback_comp l (kernel.ι d),
        Subobject.pullback_map_self]
    _ = (Subobject.pullback (Subobject.ofLE Z' Z hZ ≫ π)).obj
        (imageSubobject b) := by rw [hl]
    _ = (Subobject.pullback (Subobject.ofLE Z' Z hZ)).obj Q :=
      Subobject.pullback_comp _ _ _
    _ = (Subobject.pullback Z'.arrow).obj B' := by
      dsimp [B']
      rw [Subobject.exists_iso_map, ← Subobject.ofLE_arrow hZ,
        Subobject.pullback_comp, Subobject.pullback_map_self]
    _ = Subobject.mk (Subobject.ofLE B' Z' hBZ') := hBpull

end CategoryTheory
