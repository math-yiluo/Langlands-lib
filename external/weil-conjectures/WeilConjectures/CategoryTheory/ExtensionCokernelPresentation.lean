/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Cokernel presentation of an extension from a lifted presentation

Source: Stacks Project, Modules on Sites, Tag 093U (3).
(auxiliary; not a blueprint node).
-/

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace CategoryTheory

/-- A lift of a presentation of the quotient presents the middle term as a cokernel.
Source: Stacks Project, Modules on Sites, Tag 093U (3).
(auxiliary; not a blueprint node).

Proof: Exactness factors the composite from the relation object through the subobject.
The map from the biproduct to the middle term is epi: a map killing it kills the subobject,
hence factors through the quotient, and then is zero since the presentation is epi.
The map from the relation object to the biproduct is its kernel: the second projection of
a map killed by the biproduct map factors uniquely through the relation object; monicity
of the subobject map forces the first projection. In an abelian category an epi is the
cokernel of its kernel, giving the asserted isomorphism. -/
theorem exists_cokernel_presentation_of_lift {D : Type u} [Category.{v} D] [Abelian D]
    {M E N K P : D} (i : M ⟶ E) (p : E ⟶ N) (k : K ⟶ P) (q : P ⟶ N)
    (hip : i ≫ p = 0) (hkq : k ≫ q = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact)
    (hT : (ShortComplex.mk k q hkq).ShortExact)
    (l : P ⟶ E) (hl : l ≫ p = q) :
    ∃ g : K ⟶ M, g ≫ i = k ≫ l ∧
      Nonempty (E ≅ cokernel (biprod.lift (-g) k)) := by
  have : Mono i := hS.mono_f
  have : Mono k := hT.mono_f
  have : Epi p := hS.epi_g
  have : Epi q := hT.epi_g
  obtain ⟨g, hg⟩ := KernelFork.IsLimit.lift' hS.fIsKernel (k ≫ l)
    (by rw [Category.assoc, hl, hkq])
  change g ≫ i = k ≫ l at hg
  let a := biprod.lift (-g) k
  let b := biprod.desc i l
  have hab : a ≫ b = 0 := by simp [a, b, hg]
  have hb : Epi b := by
    apply epi_of_cancel_zero
    intro Z t ht
    have hit : i ≫ t = 0 := by
      simpa [b] using congrArg (fun z ↦ biprod.inl ≫ z) ht
    have hlt : l ≫ t = 0 := by
      simpa [b] using congrArg (fun z ↦ biprod.inr ≫ z) ht
    obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel t hit
    change p ≫ d = t at hd
    have hqd : q ≫ d = 0 := by rw [← hl, Category.assoc, hd, hlt]
    have hd0 : d = 0 := (cancel_epi q).1 (by simpa using hqd)
    rw [← hd, hd0, comp_zero]
  have ha : Mono a := mono_of_mono_fac (by simp [a] : a ≫ biprod.snd = k)
  have hker : IsLimit (KernelFork.ofι a hab) := by
    apply KernelFork.IsLimit.ofι'
    intro Z z hz
    have hzq : (z ≫ biprod.snd) ≫ q = 0 := by
      have hzp := congrArg (fun t ↦ t ≫ p) hz
      simpa [b, biprod.desc_eq, comp_add, add_comp, Category.assoc, hip, hl] using hzp
    obtain ⟨w, hw⟩ := KernelFork.IsLimit.lift' hT.fIsKernel (z ≫ biprod.snd) hzq
    change w ≫ k = z ≫ biprod.snd at hw
    refine ⟨w, ?_⟩
    apply biprod.hom_ext
    · simp only [a, Category.assoc, biprod.lift_fst, comp_neg]
      apply (cancel_mono i).1
      rw [neg_comp, Category.assoc, hg, ← Category.assoc, hw]
      apply neg_eq_iff_add_eq_zero.mpr
      simpa [b, biprod.desc_eq, comp_add, Category.assoc, add_comm] using hz
    · simpa [a] using hw
  have hc := Abelian.epiIsCokernelOfKernel (KernelFork.ofι a hab) hker
  exact ⟨g, hg, ⟨(IsColimit.coconePointUniqueUpToIso hc (colimit.isColimit _))⟩⟩

end CategoryTheory
