/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineTensorPullbackHomologySheafIso
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Sheaf-level affine ordinary tensor homology coordinates

Source: Stacks Project, Tag 01I9.
(blueprint: new-lem-pc-affine-base-change-global-sections-factorization). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Factorization of the affine global-sections coordinate before localization.
Source: Stacks Project, Tags 01I9 and 0DJ8; the coordinate is defined in
`affineBaseChangeTildeCohomologyIso`.
(blueprint: new-lem-pc-affine-base-change-global-sections-factorization).
Proof: write C for the scalar-extended complex and delta for the termwise
pullback comparison. The coordinate's sheaf isomorphism is the inverse exact
 tilde homology map, then the inverse derived homology factorization, then
homology of delta inverse, the inverse derived counit, and the representative e.
Its first three factors are affineTensorPullbackHomologySheafIso. The hom map of
an isomorphism composite is the composite of its hom maps. Homology and global
sections preserve composition, and mapIso has the corresponding forward map.
The remaining leading factor is tilde.isoTop(C.homology i). Thus the forward
global-sections map factors exactly as displayed. No localization, prime,
quasi-coherence of the final derived object, or flatness is needed. -/
theorem affineBaseChangeTildeCohomologyIso_globalSections_factorization
    (A A' : Type u) [CommRing A] [CommRing A'] (φg' : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)))) (i : ℤ) :
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
    let C := ((ModuleCat.extendScalars φg').mapHomologicalComplex (.up ℤ)).obj M
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i
    let d := affineTensorPullbackHomologySheafIso A A' φg' M i
    let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace) :=
      Scheme.Modules.tensorPullback (Spec.map (CommRingCat.ofHom φg'))
    letI : E.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w}
      (Spec.map (CommRingCat.ofHom φg'))
    let c :=
      (DerivedCategory.quotientCompQhIso.{w} _).inv.app
        ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((E.mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
      inv ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (derivedPullback (Spec.map (CommRingCat.ofHom φg'))).map
        ((DerivedCategory.quotientCompQhIso _).hom.app P)
    (affineBaseChangeTildeCohomologyIso A A' φg' K M e hc i).hom =
      (tilde.isoTop (R := .of A') (C.homology i)).hom ≫
        (moduleSpecΓFunctor (R := .of A')).map
          (d.hom ≫ H.map c ≫
            H.map ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).map e.hom)) := by
  dsimp only
  unfold affineBaseChangeTildeCohomologyIso affineTensorPullbackHomologySheafIso
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry
