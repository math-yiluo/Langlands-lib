/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageCoherence
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageCoherence
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageScalarModels
import WeilConjectures.CategoryTheory.Adjunction.MateRestrictionComparison
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # The finite-free scalar mate of restriction and direct image

For a morphism `g : U ⟶ V` of schemes and a map of ring sheaves on `V` (with its pullback
to `U`) along which the target ring is finite free, the inverse scalar mate of the canonical
restriction/direct-image comparison is invertible.

Source: Stacks Project, Tags 0B56 and 07A6.
(blueprint: lem-pur-finite-free-restriction-direct-image-mate).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

/-- The inverse scalar mate of the canonical restriction/direct-image square is invertible
for a globally finite-free coefficient extension.

Source: Stacks Project, Tags 0B56 (projection formula) and 07A6 (derived adjunction).
(blueprint: lem-pur-finite-free-restriction-direct-image-mate).

Proof: replace the finite-product basis by a coproduct basis indexed by `ULift (Fin d)`.
The finite-free direct-image coherence theorem proves that the comparison for its
normalized scalar models is invertible. The iterated-mates identity identifies its
mate with the inverse canonical restriction/direct-image square. Invertibility of an
inverse mate does not depend on the chosen left adjoints of scalar restriction. -/
theorem restrictionDirectImageMate_isIso {U V : Scheme.{u}} (g : U ⟶ V)
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj SV ≅ SU)
    (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map aV ≫ cS.hom)
    (d : ℕ)
    (hfree : Nonempty
      ((pbcRestrict aV).obj (SheafOfModules.unit ((adicLisseForget V).obj SV)) ≅
        ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget V).obj RV))) :
    IsIso (((mateEquiv (pbcDerivedScalarAdjunction aU)
      (pbcDerivedScalarAdjunction aV)).symm
        (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionDerivedDirectImage g
          RV SV RU SU aV aU cR cS comm).inv))) := by
  classical
  let R' : Coefficients g := ⟨RV, RU, cR⟩
  let S' : Coefficients g := ⟨SV, SU, cS⟩
  let a' : CoefficientMap R' S' := ⟨aV, aU, comm⟩
  obtain ⟨sV⟩ := finiteFreeDirectImageScalarModels V
  obtain ⟨sU⟩ := finiteFreeDirectImageScalarModels U
  obtain ⟨b⟩ := hfree
  let N := SheafOfModules.unit ((adicLisseForget V).obj RV)
  let : HasBiproduct (fun _ : Fin d ↦ N) := HasBiproduct.of_hasProduct _
  let e : (∏ᶜ fun _ : Fin d ↦ N) ≅
      SheafOfModules.free (R := (adicLisseForget V).obj RV) (ULift.{u + 1} (Fin d)) :=
    (biproduct.isoProduct (fun _ : Fin d ↦ N)).symm ≪≫
      biproduct.isoCoproduct (fun _ : Fin d ↦ N) ≪≫
        Sigma.whiskerEquiv Equiv.ulift.symm (fun _ ↦ Iso.refl N)
  have (M : DerivedCategory (proEtaleRingModules U RU)) :
      IsIso ((comparison sV sU a').app M) :=
    comparison_isIso_app g sV sU R' S' a' d ⟨b ≪≫ e⟩ M
  have : IsIso (comparison sV sU a') := NatIso.isIso_of_isIso_app _
  let δ := proEtaleRingRestrictionDerivedDirectImage g RV SV RU SU aV aU cR cS comm
  have hm : (mateEquiv (sU.adjunction a'.source) (sV.adjunction a'.target)
      (TwoSquare.mk _ _ _ _ (comparison sV sU a'))) = δ.inv := by
    rw [comparison, iterated_mateEquiv_conjugateEquiv]
    exact (conjugateEquiv _ _).apply_symm_apply δ.inv
  have he : ((mateEquiv (sU.adjunction a'.source) (sV.adjunction a'.target)).symm
      (TwoSquare.mk _ _ _ _ δ.inv)) = comparison sV sU a' := by
    apply (mateEquiv (sU.adjunction a'.source) (sV.adjunction a'.target)).injective
    rw [Equiv.apply_symm_apply]
    ext X
    exact (NatTrans.congr_app hm X).symm
  have : IsIso (((mateEquiv (sU.adjunction a'.source)
      (sV.adjunction a'.target)).symm (TwoSquare.mk _ _ _ _ δ.inv))) := by
    rw [he]
    infer_instance
  exact isIso_mateEquiv_symm_of_isIso
    (pbcDerivedScalarAdjunction aU) (pbcDerivedScalarAdjunction aV)
    (sU.adjunction a'.source) (sV.adjunction a'.target) (TwoSquare.mk _ _ _ _ δ.inv)

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
