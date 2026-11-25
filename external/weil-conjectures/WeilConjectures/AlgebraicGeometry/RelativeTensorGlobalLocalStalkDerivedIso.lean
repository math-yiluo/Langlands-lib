/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-! # RelativeTensorGlobalLocalStalkDerivedIso

(blueprint: lem-pc-relative-tensor-global-local-stalk-derived-iso).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Derived comparison of the global module stalk and an open local model.
Source: Stacks Project, Modules Tag 01AG; Sheaves Tags 008H and 0098;
Cohomology of Sheaves Tag 08CG.
Proof: neighbourhoods of y contained in V are cofinal among neighbourhoods of y.
The resulting natural stalk comparison identifies the composite of restriction
to the slice over V and openModuleStalkFunctor with the global module stalk.
The open immersion stalk map in the latter functor is exactly the scalar
transport of this comparison. Both functors are exact, hence their comparison
induces an isomorphism of derived functors compatible with Q. Apply the
open stalk derived functor to eL and compose with the comparison at QK.
Finally apply exact restriction of scalars along f.stalkMap y and its
commutation isomorphism with Q. The result is the displayed isomorphism.
The construction requires only y in V and is valid also for zero or acyclic
complexes; there are no degree bounds.
(blueprint: lem-pc-relative-tensor-global-local-stalk-derived-iso). -/
theorem relativeTensor_global_local_stalk_derived_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (V : X.Opens)
    (L : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ)
    (eL : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj L))
    (y : X) (hy : y ∈ V)
    [HasDerivedCategory.{v} (ModuleCat.{u} (Y.presheaf.stalk (f y)))] :
    Nonempty (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars (f.stalkMap y).hom).mapHomologicalComplex
        (.up ℤ)).obj
          (((RingedSpace.moduleStalkFunctor X.toRingedSpace y).mapHomologicalComplex
            (.up ℤ)).obj K)) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (f.stalkMap y).hom).mapHomologicalComplex
          (.up ℤ)).obj
            (((openModuleStalkFunctor X V ⟨y, hy⟩).mapHomologicalComplex
              (.up ℤ)).obj L))) := by
  let F := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V
  let S := openModuleStalkFunctor X V ⟨y, hy⟩ ⋙
    ModuleCat.restrictScalars (f.stalkMap y).hom
  let Fc := F.mapHomologicalComplex (.up ℤ)
  obtain ⟨e⟩ := eL
  let eD := (S.mapDerivedCategoryFactors.app (Fc.obj K)).symm ≪≫
    S.mapDerivedCategory.mapIso ((F.mapDerivedCategoryFactors.app K).symm ≪≫ e) ≪≫
      S.mapDerivedCategoryFactors.app L
  have hc : Nonempty ((((RingedSpace.moduleStalkFunctor X.toRingedSpace y).mapHomologicalComplex
      (.up ℤ)).obj K) ≅
      (((openModuleStalkFunctor X V ⟨y, hy⟩).mapHomologicalComplex
        (.up ℤ)).obj (Fc.obj K))) := by
    let j := V.ι
    let ρ := (j.stalkMap ⟨y, hy⟩).hom
    let U := ModuleCat.restrictScalars ρ
    have : U.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
      (RingEquiv.ofBijective ρ (ConcreteCategory.bijective_of_isIso (j.stalkMap ⟨y, hy⟩)))
    let G := RingedSpace.moduleStalkFunctor X.toRingedSpace y
    let T := RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace ⟨y, hy⟩
    obtain ⟨a⟩ := nonempty_restriction_stalk_extension_iso j ⟨y, hy⟩ K
    let unit := (NatIso.mapHomologicalComplex
      (asIso (ModuleCat.extendRestrictScalarsAdj ρ).unit) (.up ℤ)).app
        ((G.mapHomologicalComplex (.up ℤ)).obj K)
    have : (SheafOfModules.overFunctor X.ringCatSheaf V).Additive :=
      Functor.additive_of_preserves_binary_products _
    have : (Scheme.Modules.overEquiv V).functor.Additive :=
      Functor.additive_of_preserves_binary_products _
    have : (Scheme.Modules.restrictFunctor V.ι).Additive :=
      Functor.additive_of_iso (Scheme.Modules.overFunctorEquiv V)
    let b := (NatIso.mapHomologicalComplex (Scheme.Modules.overFunctorEquiv V)
      (.up ℤ)).app K
    let h := unit ≪≫ (U.mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
      ((T ⋙ U).mapHomologicalComplex (.up ℤ)).mapIso b.symm
    change Nonempty _
    exact ⟨h⟩
  obtain ⟨c⟩ := hc
  let R := (ModuleCat.restrictScalars (f.stalkMap y).hom).mapHomologicalComplex (.up ℤ)
  exact ⟨DerivedCategory.Q.mapIso (R.mapIso c) ≪≫ eD⟩

end AlgebraicGeometry.Scheme
