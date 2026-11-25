/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Ext vanishing along a finite subobject filtration

Source: latest blueprint, rational Ext proof, contravariant filtration induction.
(blueprint: lem-rational-ext-finite-filtration).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w v u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

private theorem subsingleton_of_source_iso {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {A B N : C} {q : ℕ} (e : A ≅ B)
    (h : Subsingleton (Ext A N q)) : Subsingleton (Ext B N q) := by
  refine ⟨fun x y ↦ ?_⟩
  have hh := h.elim ((mk₀ e.hom).comp x (zero_add q))
    ((mk₀ e.hom).comp y (zero_add q))
  have hh' := congrArg (fun z ↦ (mk₀ e.inv).comp z (zero_add q)) hh
  simpa only [mk₀_comp_mk₀_assoc, e.inv_hom_id, mk₀_id_comp] using hh'

private theorem subsingleton_of_source_zero {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {A N : C} {q : ℕ} (h : IsZero A) : Subsingleton (Ext A N q) := by
  have hz (x : Ext A N q) : x = 0 := by
    rw [← mk₀_id_comp x, h.eq_of_src (𝟙 A) 0, mk₀_zero, zero_comp]
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

/-- Ext from an object vanishes if it vanishes from each quotient of a finite filtration.
Source: latest blueprint, rational Ext proof, source filtration induction, and Mathlib's
contravariant Ext exact sequence (blueprint: lem-rational-ext-finite-filtration).

Proof: The bottom subobject has zero underlying object, so its Ext is zero in every
degree. At a successor the subobject inclusion is monic and its cokernel gives a short
exact sequence. Exactness of Ext in the first variable makes every class in the middle
come from the quotient, because its image in the previous subobject is zero. The
quotient's Ext is zero, so the middle class is zero. Induct over the finite index. The
top subobject is isomorphic to the whole object, and Ext transports along this iso.
This proof includes filtrations of length zero. -/
theorem finiteSubobjectFiltration {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] (M N : C) (q n : ℕ) (F : Fin (n + 1) → Subobject M)
    (hstep : ∀ a : Fin n, F a.castSucc ≤ F a.succ)
    (hbot : F 0 = ⊥) (htop : F (Fin.last n) = ⊤)
    (hquot : ∀ a : Fin n,
      Subsingleton (Ext (cokernel (Subobject.ofLE _ _ (hstep a))) N q)) :
    Subsingleton (Ext M N q) := by
  have hF (a : Fin (n + 1)) : Subsingleton (Ext (F a : C) N q) := by
    induction a using Fin.induction with
    | zero =>
      rw [hbot]
      exact subsingleton_of_source_zero
        (initialIsInitial.isZero.of_iso Subobject.botCoeIsoInitial)
    | succ a ih =>
      let f := Subobject.ofLE _ _ (hstep a)
      let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f) }
      have hz (x : Ext (F a.succ : C) N q) : x = 0 := by
        obtain ⟨z, hz⟩ := contravariant_sequence_exact₂ hS N x (ih.elim _ _)
        rw [← hz, (hquot a).elim z 0, comp_zero]
      exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
  exact subsingleton_of_source_iso
    (Subobject.isoOfEq _ _ htop ≪≫ Subobject.underlyingIso (𝟙 M)) (hF _)

/-- Isomorphic models for the successive quotients suffice in finite Ext devissage.
Source: the same finite-filtration argument, transporting the quotient groups along
isomorphisms (blueprint: lem-rational-ext-finite-filtration).

Proof: transport each quotient's Ext vanishing along its specified source isomorphism,
then apply the finite subobject filtration theorem. -/
theorem finiteSubobjectFiltrationOfIso {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] (M N : C) (q n : ℕ) (F : Fin (n + 1) → Subobject M)
    (hstep : ∀ a : Fin n, F a.castSucc ≤ F a.succ)
    (hbot : F 0 = ⊥) (htop : F (Fin.last n) = ⊤) (G : Fin n → C)
    (hiso : ∀ a : Fin n,
      Nonempty (cokernel (Subobject.ofLE _ _ (hstep a)) ≅ G a))
    (hquot : ∀ a : Fin n, Subsingleton (Ext (G a) N q)) :
    Subsingleton (Ext M N q) := by
  apply finiteSubobjectFiltration M N q n F hstep hbot htop
  intro a
  obtain ⟨e⟩ := hiso a
  exact subsingleton_of_source_iso e.symm (hquot a)

private theorem subsingleton_of_target_iso {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {A B M : C} {q : ℕ} (e : A ≅ B)
    (h : Subsingleton (Ext M A q)) : Subsingleton (Ext M B q) := by
  refine ⟨fun x y ↦ ?_⟩
  have hh := h.elim (x.comp (mk₀ e.inv) (add_zero q))
    (y.comp (mk₀ e.inv) (add_zero q))
  have hh' := congrArg (fun z ↦ z.comp (mk₀ e.hom) (add_zero q)) hh
  simpa only [comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, e.inv_hom_id,
    comp_mk₀_id] using hh'

private theorem subsingleton_of_target_zero {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {A M : C} {q : ℕ} (h : IsZero A) : Subsingleton (Ext M A q) := by
  have hz (x : Ext M A q) : x = 0 := by
    rw [← comp_mk₀_id x, h.eq_of_tgt (𝟙 A) 0, mk₀_zero, comp_zero]
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

/-- Ext into an object vanishes if it vanishes into every finite-filtration quotient.
Source: latest blueprint, rational Ext proof, covariant target devissage
(blueprint: lem-rational-ext-finite-filtration).

Proof: The bottom underlying object is zero. At a successor, the image of a middle
Ext class in the quotient Ext vanishes. Covariant exactness lifts the class to Ext
into the preceding subobject, which vanishes by induction. The given isomorphisms
transport quotient vanishing, and the top subobject is isomorphic to N. -/
theorem finiteTargetSubobjectFiltrationOfIso {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] (M N : C) (q n : ℕ) (F : Fin (n + 1) → Subobject N)
    (hstep : ∀ a : Fin n, F a.castSucc ≤ F a.succ)
    (hbot : F 0 = ⊥) (htop : F (Fin.last n) = ⊤) (G : Fin n → C)
    (hiso : ∀ a : Fin n,
      Nonempty (cokernel (Subobject.ofLE _ _ (hstep a)) ≅ G a))
    (hquot : ∀ a : Fin n, Subsingleton (Ext M (G a) q)) :
    Subsingleton (Ext M N q) := by
  have hQ (a : Fin n) :
      Subsingleton (Ext M (cokernel (Subobject.ofLE _ _ (hstep a))) q) := by
    obtain ⟨e⟩ := hiso a
    exact subsingleton_of_target_iso e.symm (hquot a)
  have hF (a : Fin (n + 1)) : Subsingleton (Ext M (F a : C) q) := by
    induction a using Fin.induction with
    | zero =>
      rw [hbot]
      exact subsingleton_of_target_zero
        (initialIsInitial.isZero.of_iso Subobject.botCoeIsoInitial)
    | succ a ih =>
      let f := Subobject.ofLE _ _ (hstep a)
      let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f) }
      have hz (x : Ext M (F a.succ : C) q) : x = 0 := by
        obtain ⟨z, hz⟩ := covariant_sequence_exact₂ M hS x ((hQ a).elim _ _)
        rw [← hz, ih.elim z 0, zero_comp]
      exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
  exact subsingleton_of_target_iso
    (Subobject.isoOfEq _ _ htop ≪≫ Subobject.underlyingIso (𝟙 N)) (hF _)

end CategoryTheory.Abelian.Ext
