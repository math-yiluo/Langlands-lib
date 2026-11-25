/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.RingedSpacePastedUnitKFlatHom

/-!
# Acyclicity of a direct image of a K-injective complex

Source: Stacks Project, Cohomology, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-pc-ringed-space-direct-image-kinjective-acyclic).
-/

@[expose] public section

universe u wY wZ

open CategoryTheory

set_option autoImplicit false

namespace AlgebraicGeometry.RingedSpace

/-- Direct image of a K-injective complex is acyclic for a subsequent direct image.
This asserts invertibility only on these particular complexes; it does not assert
that module direct image preserves K-injectivity.
Source: Stacks Project, Cohomology, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-pc-ringed-space-direct-image-kinjective-acyclic).

Proof: test the pasted units on localized K-flat complexes using
`moduleDirectImage_pastedUnit_kFlat_hom_bijective`. Every derived object is
isomorphic to a localized K-flat complex, by essential surjectivity of the
localization and `exists_isKFlatResolution`. Precomposition by this isomorphism
transfers both injectivity and surjectivity of the Hom test to every derived
object. Yoneda makes the pasted unit invertible. Its second factor is derived
direct image of the unit at I, which is invertible since I is K-injective.
Cancel this factor to obtain the asserted invertibility. -/
theorem isIso_moduleDirectImage_unit_on_kInjective
    {X Y Z : RingedSpace.{u}}
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [I.IsKInjective] :
    IsIso ((moduleDirectImage g).rightDerivedFunctorUnit.app
      (((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X))
  let J := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
  let α := (moduleDirectImage g).rightDerivedFunctorUnit.app
    (((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ)).obj J)
  let β := (derivedModuleDirectImage g).map
    ((moduleDirectImage f).rightDerivedFunctorUnit.app J)
  have : IsIso β := by
    dsimp [β, J]
    infer_instance
  have hpaste : IsIso (α ≫ β) := by
    apply isIso_of_yoneda_map_bijective
    intro T
    let G := DerivedCategory.Q.objPreimage T
    obtain ⟨K, s, hK, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution G
    have : QuasiIso s := hs
    let e : DerivedCategory.Q.obj K ≅ T :=
      asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso T
    have h := moduleDirectImage_pastedUnit_kFlat_hom_bijective f g I K hK
    change Function.Bijective (fun a => a ≫ (α ≫ β)) at h
    constructor
    · intro a b hab
      have hab' : e.hom ≫ a = e.hom ≫ b := h.1 (by
        simpa only [Category.assoc] using congrArg (fun c => e.hom ≫ c) hab)
      exact (cancel_epi e.hom).mp hab'
    · intro b
      obtain ⟨a, ha⟩ := h.2 (e.hom ≫ b)
      refine ⟨e.inv ≫ a, ?_⟩
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
        congrArg (fun c => e.inv ≫ c) ha
  exact IsIso.of_isIso_comp_right α β

end AlgebraicGeometry.RingedSpace
