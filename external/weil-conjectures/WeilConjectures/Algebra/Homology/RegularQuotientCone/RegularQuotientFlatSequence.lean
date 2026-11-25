/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.Algebra.Homology.IndependentExtensionTensor.ExtensionTensorComparisonIndependent

/-! # The coefficient quotient sequence tensored with a flat module

Source: Stacks Project, Cohomology on Sites, Tags 06YP and 06YY.
(blueprint: lem-cbc-regular-quotient-flat-sequence).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings

namespace SheafOfModules.RegularQuotientCone
open SheafOfModules.IndependentExtensionTensor

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)

attribute [local instance] isMonoidal_W_independentCoefficients
attribute [local instance] monoidalCategory
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

/-- A normalized coefficient unit yields the principal quotient short exact sequence
on any flat module, without requiring quotient maps to be surjective on sections.

Source: Stacks Project, Tags 06YP and 06YY
(blueprint: lem-cbc-regular-quotient-flat-sequence).

Proof: Tensor the coefficient-ring short exact sequence with M, using its exact tensor
functor. The normalized regular-tensor isomorphism identifies both first terms with M;
the extension-tensor comparison identifies the third with restricted scalar extension.
On the inverse regular unitor, multiplication by t sends 1 tensor x to t tensor x,
which is 1 tensor tx by balance. The quotient map sends 1 tensor x to 1 tensor x,
which is the specified coefficient unit. Thus these three isomorphisms identify the
short exact sequence with the one displayed. Sheafification and tensor normalization
prove the identities on every section of M; no sections of the quotient are lifted. -/
theorem coefficient_shortExact_of_flat
    (ht : (scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)) ≫
      ringMap φ = 0)
    (hexact : (ShortComplex.mk
      ((scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)))
      (ringMap φ) ht).ShortExact)
    (M : Modules R)
    (hflat : exactFunctor _ _ (tensorRight M))
    (η : M ⟶ (restriction φ).obj (changeOfRings φ M))
    (hη : ∀ (U : Cᵒᵖ) (x : M.val.obj U), η.val.app U x =
      (toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))
    (hz : (scalar R t).app M ≫ η = 0) :
    (ShortComplex.mk ((scalar R t).app M) η hz).ShortExact := by
  classical
  let e := regularTensorIso M
  obtain ⟨s, hs⟩ := exists_extensionTensorComparison φ M
  let T := (ShortComplex.mk
    ((scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)))
    (ringMap φ) ht).map (tensorRight M)
  have hf : (scalar R t).app M ≫ e.inv =
      e.inv ≫ (tensorRight M).map
        ((scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R))) := by
    ext U x
    let a : R.obj.obj U := t.val U
    change (regularTensorIso M).inv.val.app U (a • x) =
      (((scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R))) ▷ M).val.app U
        ((regularTensorIso M).inv.val.app U x)
    let μ := (scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R))
    have hn := tensorPresheafUnit_whiskerRight_apply (R := R)
      (L := unit (derivedChangeRingIndependentCoefficients J R))
      (L' := unit (derivedChangeRingIndependentCoefficients J R)) μ M U
      (1 : R.obj.obj U) x
    have hb : (1 : R.obj.obj U) ⊗ₜ[R.obj.obj U] (a • x) =
        (a • (1 : R.obj.obj U)) ⊗ₜ[R.obj.obj U] x :=
      TensorProduct.tmul_smul (R := R.obj.obj U) a (1 : R.obj.obj U) x
    calc
      _ = (tensorPresheafUnit (R := R)
          (unit (derivedChangeRingIndependentCoefficients J R)) M).app U
          ((1 : R.obj.obj U) ⊗ₜ[R.obj.obj U] (a • x)) :=
        regularTensorIso_inv_apply (R := R) M U (a • x)
      _ = (tensorPresheafUnit (R := R)
          (unit (derivedChangeRingIndependentCoefficients J R)) M).app U
          ((a • (1 : R.obj.obj U)) ⊗ₜ[R.obj.obj U] x) :=
        congrArg (fun z ↦ (tensorPresheafUnit (R := R)
          (unit (derivedChangeRingIndependentCoefficients J R)) M).app U z) hb
      _ = ((μ ▷ M).val.app U)
          ((tensorPresheafUnit (R := R)
            (unit (derivedChangeRingIndependentCoefficients J R)) M).app U
            ((1 : R.obj.obj U) ⊗ₜ[R.obj.obj U] x)) :=
        hn.symm
      _ = _ := congrArg (fun z ↦ ((μ ▷ M).val.app U) z)
        (regularTensorIso_inv_apply (R := R) M U x).symm
  have hg : η = e.inv ≫ (tensorRight M).map (ringMap φ) ≫ s.hom := by
    ext U x
    change η.val.app U x = s.hom.val.app U
      (((ringMap φ) ▷ M).val.app U ((regularTensorIso M).inv.val.app U x))
    have h1 : (ringMap φ).val.app U (1 : R.obj.obj U) =
        (show ((restriction φ).obj
          (unit (derivedChangeRingIndependentCoefficients J S))).val.obj U
          from (1 : S.obj.obj U)) := by
      change (φ.hom.app U).hom 1 * 1 = 1
      rw [map_one, one_mul]
    have hn := tensorPresheafUnit_whiskerRight_apply (R := R) (ringMap φ)
      M U (1 : R.obj.obj U) x
    rw [h1] at hn
    calc
      _ = _ := hη U x
      _ = s.hom.val.app U ((tensorPresheafUnit _ M).app U
          ((show ((restriction φ).obj
            (unit (derivedChangeRingIndependentCoefficients J S))).val.obj U
            from (1 : S.obj.obj U)) ⊗ₜ[R.obj.obj U] x)) := (hs U 1 x).symm
      _ = s.hom.val.app U (((ringMap φ) ▷ M).val.app U
          ((tensorPresheafUnit _ M).app U ((1 : R.obj.obj U) ⊗ₜ[R.obj.obj U] x))) :=
        congrArg (fun z ↦ s.hom.val.app U z) hn.symm
      _ = _ := congrArg (fun z ↦ s.hom.val.app U (((ringMap φ) ▷ M).val.app U z))
        (regularTensorIso_inv_apply (R := R) M U x).symm
  let a : T ≅ ShortComplex.mk ((scalar R t).app M) η hz :=
    ShortComplex.isoMk e e s (by
      change e.hom ≫ (scalar R t).app M =
        (tensorRight M).map
          ((scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R))) ≫ e.hom
      apply (cancel_mono e.inv).1
      rw [Category.assoc, hf]
      erw [Iso.hom_inv_id_assoc]
      rw [Category.assoc]
      erw [Iso.hom_inv_id, Category.comp_id])
      (by
        change e.hom ≫ η = (tensorRight M).map (ringMap φ) ≫ s.hom
        rw [hg]
        erw [Iso.hom_inv_id_assoc])
  have : PreservesFiniteLimits (tensorRight M) := hflat.1
  have : PreservesFiniteColimits (tensorRight M) := hflat.2
  exact ShortComplex.shortExact_of_iso a (hexact.map_of_exact (tensorRight M))

end SheafOfModules.RegularQuotientCone
