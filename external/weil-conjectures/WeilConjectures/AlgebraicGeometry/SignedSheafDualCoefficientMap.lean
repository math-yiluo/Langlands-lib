/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexToSingle

/-! # Postcomposition on a signed internal dual complex

Source: Stacks Project, Tag 0A8X, differential of Hom complexes. -/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {R : Sheaf J CommRingCat.{u}}

/-- Postcomposition commutes with signed precomposition.
Source: Stacks Project, Tag 0A8X. 
(blueprint: new-g3-signed-sheaf-dual-coefficient-map)
-/
theorem signedSheafDualCoefficientMap_comm
    (L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    {N N' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (g : N ⟶ N') (k : ℤ) :
    SheafOfModules.homObjMap (𝟙 (L.X (-k))) g ≫
        (signedSheafDualComplex (R := R) L N').d k (k + 1) =
      (signedSheafDualComplex (R := R) L N).d k (k + 1) ≫
        SheafOfModules.homObjMap (𝟙 (L.X (-(k + 1)))) g := by
  simp only [signedSheafDualComplex, CochainComplex.of_d,
    Linear.comp_units_smul, Linear.units_smul_comp,
    SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp, Category.comp_id]

/-- The coefficient map is actual postcomposition in every degree.
Source: Stacks Project, Tag 0A8X.
(blueprint: new-g3-signed-sheaf-dual-coefficient-map). -/
noncomputable def signedSheafDualCoefficientMap
    (L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    {N N' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (g : N ⟶ N') :
    signedSheafDualComplex (R := R) L N ⟶ signedSheafDualComplex (R := R) L N' :=
  CochainComplex.ofHom (fun k ↦ SheafOfModules.homObjMap (𝟙 (L.X (-k))) g)
    (signedSheafDualCoefficientMap_comm L g)

end CategoryTheory
