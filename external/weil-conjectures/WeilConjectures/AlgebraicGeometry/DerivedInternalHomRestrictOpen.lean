/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.Algebra.Homology.HomComplexRestrictOpen

/-!
# Derived internal Hom commutes with restriction to opens

Source: literature/stacks-project/cohomology.tex, Lemma 08DL
(blueprint: lem-sc-derived-internal-hom-restrict-open).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
universe u w


namespace CategoryTheory

noncomputable local instance (X : RingedSpace.{u}) (U : Opens X)
    [hU : HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over U))] :
    Category.{w} (@DerivedCategory (SheafOfModules.{u}
      ((sheafCompose ((Opens.grothendieckTopology X).over U)
        (forget₂ CommRingCat RingCat)).obj (X.sheaf.over U))) _ _ hU) :=
  inferInstanceAs (Category.{w}
    (DerivedCategory (SheafOfModules.{u} ((moduleRings X).over U))))

/-- Restriction of derived internal Hom to an open agrees canonically with the
internal Hom of the restricted objects.

Source: literature/stacks-project/cohomology.tex, Lemma 08DL.
Proof:
1. Represent the second argument by a functorial K-injective resolution
   (`prop-pur-kinjective-resolutions-exist`); compute Hom using
   `def-pur-derived-internal-hom`.
2. By `lem-sc-derived-k-injective-restrict-open`, restriction preserves K-injectives.
   It is exact, so the restricted
   resolution computes the restricted derived internal Hom.
3. By `def-pur-sheaf-hom` and `def-pur-hom-complex`, the sheaf Hom complexes
   agree termwise after restriction, including products
   and differentials, giving an isomorphism in the derived category.
4. Pass the complex isomorphism to the derived category. Its components restrict
   local maps, so it is natural in both arguments and successive open inclusions.
   Representative and resolution independence follows from
   `def-pur-derived-internal-hom`.
(Uses `def-pur-derived-internal-hom` and the open restriction K-injective lemma.)
(blueprint: lem-sc-derived-internal-hom-restrict-open). -/
theorem derivedInternalHom_restrict_open
    (X : RingedSpace.{u}) (U : Opens X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [hU : HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over U))]
    (K L : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    Nonempty (
      (@derivedInternalHom.{u, w} (Over U) _
          ((Opens.grothendieckTopology X).over U) (X.sheaf.over U) hU).obj
        (op ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj K),
          ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj L)) ≅
      ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj
        ((derivedInternalHom.{u, w} (Opens.grothendieckTopology X) X.sheaf).obj
          (op K, L)))) := by
  let A := SheafOfModules.{u} (moduleRings X)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let F := SheafOfModules.overFunctor.{u} (moduleRings X) U
  let Fc := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let Kc := (DerivedCategory.Q (C := A)).objPreimage K
  let Lc := (DerivedCategory.Q (C := A)).objPreimage L
  let eK := (DerivedCategory.Q (C := A)).objObjPreimageIso K
  let eL := (DerivedCategory.Q (C := A)).objObjPreimageIso L
  let Ic := (CochainComplex.kInjectiveResolutionFunctor.{u} A).obj Lc
  let η := (CochainComplex.toKInjectiveResolution.{u} A).app Lc
  have : QuasiIso η :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A Lc).2
  have : Ic.IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A Lc
  let eI : DerivedCategory.Q.obj Ic ≅ L :=
    (asIso (DerivedCategory.Q.map η)).symm ≪≫ eL
  have : CochainComplex.IsKInjective (Fc.obj Ic) := kInjective_of_restrict_open X U Ic
  let eKU : DerivedCategory.Q.obj (Fc.obj Kc) ≅ F.mapDerivedCategory.obj K :=
    (F.mapDerivedCategoryFactors.app Kc).symm ≪≫ F.mapDerivedCategory.mapIso eK
  let eIU : DerivedCategory.Q.obj (Fc.obj Ic) ≅ F.mapDerivedCategory.obj L :=
    (F.mapDerivedCategoryFactors.app Ic).symm ≪≫ F.mapDerivedCategory.mapIso eI
  obtain ⟨eX⟩ := derivedInternalHom_obj_iso.{u, w}
    (Opens.grothendieckTopology X) X.sheaf K L Kc Ic eK eI
  obtain ⟨eU⟩ := @derivedInternalHom_obj_iso.{u, w} (Over U) _
    ((Opens.grothendieckTopology X).over U) (X.sheaf.over U) hU
    (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj L)
    (Fc.obj Kc) (Fc.obj Ic) inferInstance eKU eIU
  obtain ⟨eC⟩ := homComplex_restrict_open X U Kc Ic
  let QU := DerivedCategory.Q (C := SheafOfModules.{u} ((moduleRings X).over U))
  exact ⟨eU ≪≫ QU.mapIso eC ≪≫
    (F.mapDerivedCategoryFactors.app (homComplex (R := X.sheaf) Kc Ic)).symm ≪≫
    (F.mapDerivedCategory.mapIso eX).symm⟩

end CategoryTheory
