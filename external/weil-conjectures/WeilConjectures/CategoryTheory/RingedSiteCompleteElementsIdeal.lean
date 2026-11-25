/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.RingTheory.Ideal.Span
public import WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestriction
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementAddition
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementMultiplication
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsLocal

/-!
# Vanishing localizations form a sheaf of ideals

Source: Stacks Project, algebraization.tex, Tags 0998 and 0997
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false

namespace CategoryTheory

private theorem sectionLocalization_zero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) :
    IsZero (ringedSiteSectionLocalization R U 0) := by
  let M := SheafOfModules.unit (R.over U)
  have hz : (M.unitHomEquiv.symm
      (PresheafOfModules.sectionsMk
        (fun V ↦ R.obj.map V.unop.hom.op 0)
        (fun {V W} a ↦ ringedSiteSectionLocalization_compatible R U 0 V W a))) = 0 := by
    apply M.unitHomEquiv.injective
    ext V
    simp only [Equiv.apply_symm_apply]
    simp only [SheafOfModules.unitHomEquiv_apply_coe, map_zero]
    rfl
  change IsZero (colimit (Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ _)))
  rw [hz]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply colimit.hom_ext
  intro n
  have h := colimit.w (Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ (0 : M ⟶ M)))
    (homOfLE (Nat.le_add_right n 1))
  simpa using h.symm

open CategoryTheory.Pretriangulated.Opposite in
private theorem completeElement_zero
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) (U : C) :
    IsRingedSiteCompleteElement J R K U 0 := by
  let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let L := (DerivedCategory.singleFunctor (SheafOfModules.{u} (O.over U)) 0).obj
    (ringedSiteSectionLocalization O U 0)
  let N := ringedSiteDerivedRestriction O U K
  let : HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (R.over U))) :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} (O.over U)))
  obtain ⟨s, hs⟩ := (ringedInternalHom_exact (J.over U) (R.over U)).2 N
  let := s
  have := hs
  have hL : IsZero L := (DerivedCategory.singleFunctor _ 0).map_isZero
    (sectionLocalization_zero O U)
  exact ((Functor.curry.obj (derivedInternalHom (J.over U) (R.over U))).flip.obj N).map_isZero
    hL.op

/-- The sections whose localization has zero derived internal Hom into K form a sheaf
of ideals. The first clause identifies every ideal section with the actual Hom-vanishing
criterion. Ideals encode zero, addition, and multiplication by arbitrary sections. The
next clauses express restriction and descent for every covering sieve. The final clause
is the locally finite-generated ideal consequence, using local finite-span membership.

Source: Stacks Project, algebraization.tex, Tags 0998 and 0997
(auxiliary; not a blueprint node).

Proof: Localization at zero is the colimit of zero transition maps, hence zero.
Contravariant derived internal Hom preserves zero, proving zero membership.
The multiplication lemma identifies localization at af with the tensor of the
localizations at a and f, proves these modules flat, and applies Hom-complex
currying into a K-injective representative. The addition lemma uses the binary
localization short exact sequence for h=f+g and exactness of contravariant
RHom. The locality lemma compares slice restriction of the defining localization
and of RHom, and proves descent by applying sheaf separatedness to cohomology
sheaves on a pulled-back covering sieve. These three closure properties define
an actual Ideal with carrier the complete elements. Its restriction and local
membership properties are precisely the two parts of locality. Finally, all
locally supplied generators belong to this ideal; Ideal.span_le puts every
section of their span in it, and locality descends the resulting membership.
The zero ideal, zero ring and empty covering sieves are included.
-/
theorem ringedSite_complete_elements_ideal
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :
    ∃ I : ∀ U : C, Ideal (R.obj.obj (op U)),
      (∀ (U : C) (f : R.obj.obj (op U)),
        f ∈ I U ↔ IsRingedSiteCompleteElement J R K U f) ∧
      (∀ (U V : C) (a : V ⟶ U) (f : R.obj.obj (op U)),
        f ∈ I U → R.obj.map a.op f ∈ I V) ∧
      (∀ (U : C) (S : Sieve U), S ∈ J U → ∀ f : R.obj.obj (op U),
        (∀ (V : C) (a : V ⟶ U), S a → R.obj.map a.op f ∈ I V) → f ∈ I U) ∧
      (∀ (U : C) (S : Sieve U), S ∈ J U → ∀ x : R.obj.obj (op U),
        (∀ (V : C) (a : V ⟶ U), S a →
          ∃ (r : ℕ) (b : Fin r → R.obj.obj (op V)),
            (∀ i : Fin r, IsRingedSiteCompleteElement J R K V (b i)) ∧
            R.obj.map a.op x ∈ Ideal.span (Set.range b)) →
        IsRingedSiteCompleteElement J R K U x) := by
  have hlocal := ringedSite_completeElements_locality J R K
  let I (U : C) : Ideal (R.obj.obj (op U)) :=
    { carrier := {f | IsRingedSiteCompleteElement J R K U f}
      zero_mem' := completeElement_zero J R K U
      add_mem' := fun hf hg ↦ ringedSite_completeElement_add J R K U _ _ hf hg
      smul_mem' := fun a _ hf ↦ ringedSite_completeElement_mul J R K U a _ hf }
  refine ⟨I, fun _ _ ↦ Iff.rfl, ?_, ?_, ?_⟩
  · intro U V a f hf
    exact hlocal.1 U V a f hf
  · intro U S hS f hf
    exact hlocal.2 U S hS f hf
  · intro U S hS x hx
    apply hlocal.2 U S hS x
    intro V a ha
    obtain ⟨r, b, hb, hxb⟩ := hx V a ha
    have hspan : Ideal.span (Set.range b) ≤ I V := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hb i
    exact hspan hxb

end CategoryTheory
