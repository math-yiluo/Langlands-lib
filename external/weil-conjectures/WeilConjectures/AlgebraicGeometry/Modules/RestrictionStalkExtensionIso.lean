/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Open restriction and extension of stalk scalars

## References

* Stacks Project, Sheaves, Tag 0098
* Cohomology, Tag 06YB
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TopologicalSpace Opposite

/-- The inverse stalk ring map acts on germs through the inverse section-ring map. -/
private theorem inverse_stalkMap_germ
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X)
    (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
    (inv (j.stalkMap x)) (X.presheaf.germ U x hx r) =
      Y.presheaf.germ (j ''ᵁ U) (j x) (by simpa) ((j.appIso U).inv r) := by
  apply (ConcreteCategory.bijective_of_isIso (j.stalkMap x)).1
  simp only [IsIso.inv_hom_id_apply]
  rw [Scheme.Hom.germ_stalkMap_apply]
  change X.presheaf.germ U x hx r =
    ((j.appIso U).inv ≫ j.app _ ≫ X.presheaf.germ _ x _) r
  rw [Scheme.Hom.appIso_inv_app_assoc]
  exact (X.presheaf.germ_res_apply (eqToHom (j.preimage_image_eq U)) x
    (by simpa) r).symm

/-- The additive restriction-stalk comparison is semilinear over the inverse stalk map. -/
private theorem restriction_stalk_smul
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) (M : Y.Modules)
    (r : X.presheaf.stalk x)
    (m : ((Scheme.Modules.restrictFunctor j).obj M).presheaf.stalk x) :
    (Scheme.Modules.restrictStalkNatIso j x).hom.app M (r • m) =
      (inv (j.stalkMap x)) r •
        (show M.presheaf.stalk (j x) from
          (Scheme.Modules.restrictStalkNatIso j x).hom.app M m) := by
  let N := (Scheme.Modules.restrictFunctor j).obj M
  obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hxV, m, rfl⟩ := N.presheaf.exists_germ_eq m
  have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx r,
    ← N.presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m]
  erw [← PresheafOfModules.germ_smul (R := X.presheaf) N.val]
  rw [inverse_stalkMap_germ]
  have hg (s : Γ(N, U ⊓ V)) :
      (Scheme.Modules.restrictStalkNatIso j x).hom.app M
        (N.presheaf.germ (U ⊓ V) x hx s) =
        M.presheaf.germ (j ''ᵁ (U ⊓ V)) (j x) (by simpa) s :=
    ConcreteCategory.congr_hom
      (Scheme.Modules.germ_restrictStalkNatIso_hom_app j x M hx) s
  erw [hg, hg]
  exact PresheafOfModules.germ_smul (R := Y.presheaf) M.val _ _ _ _ _

/-- The additive stalk comparison, viewed as a linear map after restriction of scalars. -/
private noncomputable def restrictionStalkLinearMap
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) (M : Y.Modules) :
    (ModuleCat.restrictScalars (j.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
          ((Scheme.Modules.restrictFunctor j).obj M)) ⟶
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x)).obj M :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (j.stalkMap x).hom).obj
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        ((Scheme.Modules.restrictFunctor j).obj M)))
    (Y := (RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x)).obj M)
    { toFun := (Scheme.Modules.restrictStalkNatIso j x).hom.app M
      map_add' := map_add _
      map_smul' := fun r m ↦ by
        change (Scheme.Modules.restrictStalkNatIso j x).hom.app M
            ((j.stalkMap x) r •
              (show ((Scheme.Modules.restrictFunctor j).obj M).presheaf.stalk x from m)) =
          r • (show M.presheaf.stalk (j x) from
            (Scheme.Modules.restrictStalkNatIso j x).hom.app M m)
        rw [restriction_stalk_smul]
        simp }

/-- The linear stalk comparison is invertible because its underlying additive map is. -/
private noncomputable def restrictionStalkLinearIso
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) (M : Y.Modules) :
    (ModuleCat.restrictScalars (j.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
          ((Scheme.Modules.restrictFunctor j).obj M)) ≅
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x)).obj M := by
  let a := restrictionStalkLinearMap j x M
  have : IsIso a :=
    (ConcreteCategory.isIso_iff_bijective a).mpr
      (ConcreteCategory.bijective_of_isIso
        ((Scheme.Modules.restrictStalkNatIso j x).hom.app M))
  exact asIso a

/-- The linear stalk comparisons are natural in the module sheaf. -/
private noncomputable def restrictionStalkLinearNatIso
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) :
    (Scheme.Modules.restrictFunctor j ⋙ RingedSpace.moduleStalkFunctor X.toRingedSpace x) ⋙
        ModuleCat.restrictScalars (j.stalkMap x).hom ≅
      RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x) :=
  NatIso.ofComponents (restrictionStalkLinearIso j x) (by
    intro M N f
    ext m
    exact ConcreteCategory.congr_hom
      ((Scheme.Modules.restrictStalkNatIso j x).hom.naturality f) m)

/-- Stalks of open restriction are extension of scalars of the original stalks. -/
theorem nonempty_restriction_stalk_extension_iso
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X)
    (K : CochainComplex Y.Modules ℤ) :
    Nonempty
      ((((ModuleCat.extendScalars (j.stalkMap x).hom).mapHomologicalComplex (.up ℤ)).obj
        (((RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x)).mapHomologicalComplex
          (.up ℤ)).obj K)) ≅
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (.up ℤ)).obj
            (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj K))) := by
  let ρ := (j.stalkMap x).hom
  let eρ := RingEquiv.ofBijective ρ
    (ConcreteCategory.bijective_of_isIso (j.stalkMap x))
  have : (ModuleCat.restrictScalars ρ).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv eρ
  let S := Scheme.Modules.restrictFunctor j ⋙
    RingedSpace.moduleStalkFunctor X.toRingedSpace x
  have : (Scheme.Modules.restrictFunctor j).PreservesZeroMorphisms := by infer_instance
  have : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).PreservesZeroMorphisms :=
    RingedSpace.moduleStalkFunctor_preservesZeroMorphisms X.toRingedSpace x
  have : S.PreservesZeroMorphisms := by dsimp [S]; infer_instance
  let E := ModuleCat.extendScalars ρ
  let U := ModuleCat.restrictScalars ρ
  let a := restrictionStalkLinearNatIso j x
  let b : RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x) ⋙ E ≅ S :=
    Functor.isoWhiskerRight a.symm E ≪≫ Functor.associator S U E ≪≫
      Functor.isoWhiskerLeft S (asIso (ModuleCat.extendRestrictScalarsAdj ρ).counit) ≪≫
      Functor.rightUnitor S
  exact ⟨(NatIso.mapHomologicalComplex b (.up ℤ)).app K⟩

end AlgebraicGeometry
