/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.DerivedCoupleExact
import WeilConjectures.CategoryTheory.FiniteCycleDerivedComparison
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-!
# Finite exact-couple quotient kernels

Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2;
Stacks Project, Tags 011R, 011T and 0AMJ.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem incomingAlphaIter_succ (X : BigradedExactCouple C 0)
    (n : ℕ) (p q : ℤ) :
    X.incomingAlphaIter (n + 1) p q =
      X.alpha (p + (n + 1 : ℕ)) (q - (n + 1 : ℕ)) ≫
        eqToHom (by congr 1 <;> omega) ≫ X.incomingAlphaIter n p q := by
  apply eq_of_heq
  dsimp [incomingAlphaIter, alphaIter]
  simp only [Category.assoc]
  apply heq_comp rfl rfl rfl HEq.rfl
  simp only [← Category.assoc, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
  rw [heq_eqToHom_comp_iff]
  congr! 1 <;> omega

private theorem alphaIter_image (X : BigradedExactCouple C 0)
    (r : ℕ) (p q : ℤ) :
    imageSubobject (X.alphaIter r p q) =
      imageSubobject (X.incomingAlphaIter r (p - r) (q + r)) := by
  have h : X.incomingAlphaIter r (p - r) (q + r) =
      eqToHom (by congr 1 <;> omega) ≫ X.alphaIter r p q := by
    apply eq_of_heq
    unfold incomingAlphaIter
    simp only [comp_eqToHom_heq_iff]
    apply HEq.trans ?_ (eqToHom_comp_heq _ _).symm
    congr! 1 <;> omega
  rw [h, imageSubobject_iso_comp]

private theorem kernel_comp_pullback {A B D : C} (a : A ⟶ B) (b : B ⟶ D) :
    kernelSubobject (a ≫ b) = (Subobject.pullback a).obj (kernelSubobject b) := by
  simpa only [comp_zero] using (pullback_equalizer b 0 a).symm

private theorem transported_exact_g {s : ℕ} (Y : BigradedExactCouple C s)
    (a b u w : ℤ) (hu : a - 1 = u) (hw : b + 1 = w) :
    kernelSubobject (Y.g u w) =
      imageSubobject (Y.alpha a b ≫ eqToHom (congrArg₂ Y.D hu hw)) := by
  subst u
  subst w
  simpa only [eqToHom_refl, Category.comp_id] using (Y.exact_g a b).symm

private theorem g_epi_of_next_zero {s : ℕ} (Y : BigradedExactCouple C s)
    (a b : ℤ) (hz : IsZero (Y.D (a + s + 2) (b - s - 1))) : Epi (Y.g a b) := by
  have hf : Y.f (a + s) (b - s) = 0 := by
    apply IsZero.eq_of_tgt
    convert hz using 1
  have him : imageSubobject (Y.g a b) = ⊤ := by
    rw [Y.exact_f, hf, kernelSubobject_zero]
  apply Abelian.epi_of_cokernel_π_eq_zero
  apply (cancel_epi (⊤ : Subobject (Y.E (a + s) (b - s))).arrow).mp
  have hz := imageSubobject_arrow_comp_eq_zero (cokernel.condition (Y.g a b))
  rw [him] at hz
  simpa only [comp_zero] using hz

/-- The canonical finite cycle projection is epic when the following D term is zero,
and its kernel is the inverse image of the next incoming alpha image.

Proof: Identify the prescribed incoming powers in pageCouple_image with
incomingAlphaIter by their recurrences. At the endpoint of alphaIter r, this
incoming r-fold iterate has the same image as alphaIter r, since their source
transport is an isomorphism. The image formula for the monic iterated inclusion I
therefore identifies its image with that of alphaIter r. Subobject.isoOfMkEqMk
identifies the image domains; compose its hom with the actual image epimorphism
of alphaIter r to construct an epic e satisfying e followed by I = alphaIter r.
Apply finiteCycle_derived_comparison to identify e followed by transported g_r
with factorThru(initialG) followed by the canonical finite cycle projection.
Exact_g identifies the kernel of g_r with the incoming page-alpha image.
Push this subobject forward along I. Its image is that of I_(r+1), by the
successor recurrence and the epic image factorization of page-alpha, hence is the
incoming (r+1)-fold original alpha image by pageCouple_image. The kernel of a
composite is the pullback of the second kernel along the first map; prove this
using Mathlib pullback_equalizer. Pullback composition and pullback_map_self
for monic I now give the displayed pullback along e followed by I = alphaIter r.
Finally hnext makes the following f zero, so exact_f makes image(g_r) top.
Cancel the top arrow in its composite with the cokernel projection to show this
projection is zero. Thus g_r is epic, and so is its composite with e and the
endpoint isomorphism. No half-plane or colimit assumption is used.
Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2, finite image
induction, exact triangle and original-g projection; Stacks Tags 011R and 0AMJ.
(blueprint: lem-sp-finite-cycle-kernel-presentation) -/
theorem finiteCycle_kernel_presentation (X : BigradedExactCouple C 0)
    (r : ℕ) (p q : ℤ)
    (hnext : IsZero ((X.pageCouple r).D (p + 2) (q - 1)))
    (hg : (X.cycleBoundaryTower.Z r p q).Factors (X.initialG p q)) :
    Epi ((X.cycleBoundaryTower.Z r p q).factorThru (X.initialG p q) hg ≫
      X.cycleBoundaryTower.projection r p q) ∧
    kernelSubobject ((X.cycleBoundaryTower.Z r p q).factorThru
        (X.initialG p q) hg ≫ X.cycleBoundaryTower.projection r p q) =
      (Subobject.pullback (X.alphaIter r p q)).obj
        (imageSubobject (X.incomingAlphaIter (r + 1) (p - r) (q + r))) := by
  obtain ⟨A, I, hA0, hAs, hI0, hIs, hImono, hIm, _, _⟩ := pageCouple_image X
  have hA : ∀ (n : ℕ) (a b : ℤ), A n a b = X.incomingAlphaIter n a b := by
    intro n a b
    induction n with
    | zero =>
      rw [hA0]
      simp only [incomingAlphaIter, alphaIter, eqToHom_trans]
    | succ n ih => rw [hAs, ih, incomingAlphaIter_succ]
  have hi := hImono r (p - r) (q + r)
  have him : Subobject.mk (imageSubobject (X.alphaIter r p q)).arrow =
      Subobject.mk (I r (p - r) (q + r)) := by
    rw [Subobject.mk_arrow, ← imageSubobject_mono, hIm, hA, alphaIter_image]
  let j := Subobject.isoOfMkEqMk (imageSubobject (X.alphaIter r p q)).arrow
    (I r (p - r) (q + r)) him
  let e := factorThruImageSubobject (X.alphaIter r p q) ≫ j.hom
  have : Epi e := by dsimp [e]; infer_instance
  have he : e ≫ I r (p - r) (q + r) = X.alphaIter r p q := by
    dsimp [e, j]
    simp only [Category.assoc, Subobject.isoOfMkEqMk_hom, Subobject.ofMkLEMk_comp,
      imageSubobject_arrow_comp]
  have heg := finiteCycle_derived_comparison X I hI0 hIs hImono r p q hg e he
  let g := (X.pageCouple r).g (p - r) (q + r)
  have hg_epi : Epi g := by
    apply g_epi_of_next_zero
    convert hnext using 1; congr 1 <;> omega
  have hk : (Subobject.map (I r (p - r) (q + r))).obj (kernelSubobject g) =
      imageSubobject (X.incomingAlphaIter (r + 1) (p - r) (q + r)) := by
    let a := (X.pageCouple r).alpha ((p - r) + 1) ((q + r) - 1)
    let t : (X.pageCouple r).D (((p - r) + 1) - 1) (((q + r) - 1) + 1) ⟶
        (X.pageCouple r).D (p - r) (q + r) := eqToHom (by congr 1 <;> omega)
    have hker : kernelSubobject g = imageSubobject (a ≫ t) := by
      exact transported_exact_g (X.pageCouple r)
        ((p - r) + 1) ((q + r) - 1) (p - r) (q + r) (by omega) (by omega)
    rw [hker, Subobject.map_obj_eq_mk]
    have himage : imageSubobject (a ≫ eqToHom (by congr 1 <;> omega) ≫
        I r (p - r) (q + r)) = imageSubobject (I (r + 1) (p - r) (q + r)) := by
      rw [hIs]
      dsimp [derivedDInclusion]
      simp only [Category.assoc]
      change imageSubobject (a ≫ t ≫ I r (p - r) (q + r)) =
        imageSubobject (image.ι a ≫ t ≫ I r (p - r) (q + r))
      calc
        _ = imageSubobject (factorThruImage a ≫
            (image.ι a ≫ t ≫ I r (p - r) (q + r))) := by
          rw [← Category.assoc, ← Category.assoc, image.fac, Category.assoc]
        _ = _ := imageSubobject_comp_of_epi _ _
    rw [← hA, ← hIm, ← himage]
    have : StrongEpi (factorThruImageSubobject
        (a ≫ t)) := strongEpi_of_epi _
    simpa only [imageSubobject_arrow_comp_assoc, Category.assoc, t] using
      (Subobject.imageSubobject_eq_mk
        (factorThruImageSubobject (a ≫ t))
        ((imageSubobject (a ≫ t)).arrow ≫
          I r (p - r) (q + r))).symm
  constructor
  · rw [← heg]
    infer_instance
  · rw [← heg, ← Category.assoc, kernelSubobject_comp_mono]
    change kernelSubobject (e ≫ g) = _
    rw [kernel_comp_pullback, ← he, ← hk]
    conv_rhs => rw [Subobject.pullback_comp, Subobject.pullback_map_self]

end CategoryTheory.BigradedExactCouple
