/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections

/-!
# Universality of the strict reduction units

The `n`-th strict reduction unit of a module sheaf with constant coefficients is the
universal map to a module whose coefficient action factors through `A ⧸ I ^ (n + 1)`.

Source: Stacks Project, Modules on Sites, Tags 03D7 and 099L
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {A : Type u} [CommRing A] {I : Ideal A}

/-- The quotient map of constant ring sheaves is locally surjective.
Source: Stacks Project, Sites, Tag 00WM (auxiliary; not a blueprint node). -/
theorem quotient_isLocallySurjective (n : ℕ) :
    Presheaf.IsLocallySurjective J
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map (quotient J A I n)).hom := by
  rw [Presheaf.isLocallySurjective_iff_whisker_forget]
  let g := CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))
  let P := (Functor.const Cᵒᵖ).obj (CommRingCat.of A)
  let Q := (Functor.const Cᵒᵖ).obj (CommRingCat.of (A ⧸ I ^ (n + 1)))
  have hfac : toSheafify J P ≫ sheafifyMap J ((Functor.const Cᵒᵖ).map g) =
      (Functor.const Cᵒᵖ).map g ≫ toSheafify J Q :=
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map g)).symm
  have hs : Presheaf.IsLocallySurjective J ((Functor.const Cᵒᵖ).map g) :=
    Presheaf.isLocallySurjective_of_surjective _ _ (fun _ ↦ Ideal.Quotient.mk_surjective)
  have : Presheaf.IsLocallySurjective J ((Functor.const Cᵒᵖ).map g ≫ toSheafify J Q) :=
    inferInstance
  have : Presheaf.IsLocallySurjective J (sheafifyMap J ((Functor.const Cᵒᵖ).map g)) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac
  rw [Presheaf.isLocallySurjective_iff_whisker_forget] at this
  exact this

/-- The quotient maps are compatible with the finite transition maps.
Source: Stacks Project, Tag 099L (auxiliary; not a blueprint node). -/
theorem quotient_comp_transition (n : ℕ) :
    quotient J A I (n + 1) ≫ transition J A I n = quotient J A I n := by
  unfold quotient transition
  rw [← Functor.map_comp]
  rfl

variable (J A I) in
/-- Module sheaves whose coefficient action factors through the `n`-th finite quotient.
Source: Stacks Project, Modules on Sites, Tag 03D7 (auxiliary; not a blueprint node). -/
def IsReducedModule (n : ℕ) (P : Mod (coefficients J A I false)) : Prop :=
  ∃ P' : Mod (finite J A I n), Nonempty ((res (quotient J A I n)).obj P' ≅ P)

/-- A module reduced at level `n` is reduced at level `n + 1`.
Source: Stacks Project, Tag 099L (auxiliary; not a blueprint node). -/
theorem IsReducedModule.succ {n : ℕ} {P : Mod (coefficients J A I false)}
    (hP : IsReducedModule J A I n P) : IsReducedModule J A I (n + 1) P := by
  obtain ⟨P', ⟨i⟩⟩ := hP
  exact ⟨(res (transition J A I n)).obj P',
    ⟨(resCompIso _ _ _ (quotient_comp_transition n)).app P' ≪≫ i⟩⟩

/-- Restriction of scalars along a finite quotient is fully faithful.
Source: Stacks Project, Modules on Sites, Tag 03D7 (auxiliary; not a blueprint node). -/
def resQuotientFullyFaithful (n : ℕ) : (res (quotient J A I n)).FullyFaithful := by
  have := quotient_isLocallySurjective (J := J) (A := A) (I := I) n
  refine ⟨(fun {M N} f ↦
    ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective _ N.isSheaf).symm
      f.val⟩), ?_, ?_⟩
  · intro M N f
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective _ N.isSheaf).apply_symm_apply
      f.val
  · intro M N f
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective _ N.isSheaf).symm_apply_apply
      f.val

/-- The strict reduction unit is the unit of the scalar-extension adjunction.
Source: Stacks Project, Modules on Sites, Tag 03D7 (auxiliary; not a blueprint node). -/
theorem reductionUnit_app_eq (n : ℕ) (N : Mod (coefficients J A I false)) :
    ((reductionUnit J A I false).app N).app (op n) =
      (SheafOfModules.RingedTensor.tensorAdjunction (quotient J A I n)).unit.app N := by
  ext U m
  exact (reductionUnit_existsUnique J A I false).exists.choose_spec N n U m

/-- The strict reduction unit is universal among maps to reduced modules.
Source: Stacks Project, Modules on Sites, Tag 03D7 (auxiliary; not a blueprint node). -/
theorem reductionUnit_existsUnique_lift (n : ℕ) (N P : Mod (coefficients J A I false))
    (hP : IsReducedModule J A I n P) (f : N ⟶ P) :
    ∃! g : ((reductionTower J A I false).obj N).obj (op n) ⟶ P,
      ((reductionUnit J A I false).app N).app (op n) ≫ g = f := by
  obtain ⟨P', ⟨i⟩⟩ := hP
  let adj := SheafOfModules.RingedTensor.tensorAdjunction (quotient J A I n)
  let ff := resQuotientFullyFaithful (J := J) (A := A) (I := I) n
  rw [reductionUnit_app_eq]
  refine ⟨(res (quotient J A I n)).map ((adj.homEquiv _ _).symm (f ≫ i.inv)) ≫ i.hom, ?_, ?_⟩
  · dsimp only
    have key := (adj.homEquiv_unit N P' ((adj.homEquiv _ _).symm (f ≫ i.inv))).symm
    rw [Equiv.apply_symm_apply] at key
    exact ((reassoc_of% key) i.hom).trans (by rw [Iso.inv_hom_id, Category.comp_id])
  · intro g hg
    have hpre := ff.map_preimage (g ≫ i.inv)
    have key := adj.homEquiv_unit N P' (ff.preimage (g ≫ i.inv))
    have hh : (adj.homEquiv _ _) (ff.preimage (g ≫ i.inv)) = f ≫ i.inv := by
      rw [key]
      erw [hpre]
      rw [← Category.assoc]
      erw [hg]
    rw [← (adj.homEquiv _ _).eq_symm_apply] at hh
    rw [← hh]
    erw [hpre]
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The strict reduction of every module is reduced.
Source: Stacks Project, Tag 099L (auxiliary; not a blueprint node). -/
theorem isReducedModule_reductionTower (n : ℕ) (N : Mod (coefficients J A I false)) :
    IsReducedModule J A I n (((reductionTower J A I false).obj N).obj (op n)) :=
  ⟨(change (quotient J A I n)).obj N, ⟨Iso.refl _⟩⟩

end CategoryTheory.ConstantCompletion
