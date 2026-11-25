/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Algebra.Homology.StalkKFlatTensorHomology
import WeilConjectures.AlgebraicGeometry.RelativeInverseImageStalkRestriction
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Topology.Sheaves.Sheafify
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # RelativeTensorStalkGlobalHomology

(blueprint: lem-pc-relative-tensor-stalk-global-homology).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme

private theorem stalk_preservesFiniteLimits (Z : RingedSpace.{u}) (x : Z) :
    PreservesFiniteLimits (RingedSpace.moduleStalkFunctor Z x) := by
  let A : ModuleCat.{u} (Z.presheaf.stalk x) ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat.{u} (Z.presheaf.stalk x)) AddCommGrpCat.{u}
  have hb : PreservesFiniteLimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} Z.carrier ⋙
        TopCat.Presheaf.stalkFunctor (X := Z.carrier) AddCommGrpCat.{u} x) := inferInstance
  have : PreservesFiniteLimits (RingedSpace.moduleStalkFunctor Z x ⋙ A) :=
    comp_preservesFiniteLimits (SheafOfModules.toSheaf (moduleRings Z))
      (TopCat.Sheaf.forget AddCommGrpCat.{u} Z.carrier ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  exact preservesFiniteLimits_of_reflects_of_preserves _ A

private theorem stalk_preservesFiniteColimits (Z : RingedSpace.{u}) (x : Z) :
    PreservesFiniteColimits (RingedSpace.moduleStalkFunctor Z x) := by
  let A : ModuleCat.{u} (Z.presheaf.stalk x) ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat.{u} (Z.presheaf.stalk x)) AddCommGrpCat.{u}
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u} (moduleRings Z)) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful.{u, u, u, u} (moduleRings Z)).2.2.1
  have hb : PreservesFiniteColimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} Z.carrier ⋙
        TopCat.Presheaf.stalkFunctor (X := Z.carrier) AddCommGrpCat.{u} x) := inferInstance
  have : PreservesFiniteColimits (RingedSpace.moduleStalkFunctor Z x ⋙ A) :=
    comp_preservesFiniteColimits (SheafOfModules.toSheaf (moduleRings Z))
      (TopCat.Sheaf.forget AddCommGrpCat.{u} Z.carrier ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  exact preservesFiniteColimits_of_reflects_of_preserves _ A

/-- Global stalk computation for a prescribed K-flat relative representative.
Source: Stacks Project, Cohomology of Sheaves, Tags 06YB, 08CG, 09U9;
Sheaves Tags 008H and 0098; Modules Tag 01AG.
Proof: form the inverse-image ringed space with underlying space X. The canonical
inverse-image ring stalk isomorphism identifies its stalk ring with A=O_Y,f(y).
Take M to be the actual module stalk of F restricted along that isomorphism.
The stalk criterion makes P_y K-flat. Exactness of stalks sends q to a
quasi-isomorphism; the germ formula for the inverse-image ring map identifies
its target with the restriction along f.stalkMap of the module stalk of K.
A K-flat complex computes its derived tensor with every complex, so Q of the
total tensor of P_y and M[0] is isomorphic to Q of that restricted stalk of K
tensored in the derived category with M[0]. Stalks commute with total tensor,
single complexes and homology. Taking homology and forgetting scalars gives
the displayed isomorphisms for all i with this same M. This works for zero
modules, unbounded complexes and every integer i.
(blueprint: lem-pc-relative-tensor-stalk-global-homology). -/
theorem relativeTensor_stalk_global_homology_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (y : X)
    [HasDerivedCategory.{v} (ModuleCat.{u} (Y.presheaf.stalk (f y)))]
    (P : CochainComplex (SheafOfModules.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (TopCat.Sheaf.inverseImageRing f.base Y.sheaf))) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := TopCat.Sheaf.inverseImageRing f.base Y.sheaf) P)
    (q : P ⟶ ((SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
          (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) (hq : QuasiIso q) :
    ∀ F : SheafOfModules.{u} ((sheafCompose
          (Opens.grothendieckTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (TopCat.Sheaf.inverseImageRing f.base Y.sheaf)),
      ∃ M : ModuleCat.{u} (Y.presheaf.stalk (f y)), ∀ i : ℤ,
          Nonempty ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).obj
              ((SheafOfModules.toSheaf _).obj
                ((CochainComplex.mapBifunctor P
                  ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
                  (@MonoidalCategory.curriedTensor _ _ (SheafOfModules.monoidalCategory
                    (TopCat.Sheaf.inverseImageRing f.base Y.sheaf)))).homology i)) ≅
            (forget₂ (ModuleCat.{u} (Y.presheaf.stalk (f y))) AddCommGrpCat.{u}).obj
              ((DerivedCategory.homologyFunctor
                (ModuleCat.{u} (Y.presheaf.stalk (f y))) i).obj
                  (DerivedCategory.Q.obj
                    (((ModuleCat.restrictScalars (f.stalkMap y).hom).mapHomologicalComplex
                      (.up ℤ)).obj
                        (((RingedSpace.moduleStalkFunctor X.toRingedSpace y).mapHomologicalComplex
                          (.up ℤ)).obj K)) ⊗
                    (DerivedCategory.singleFunctor
                      (ModuleCat.{u} (Y.presheaf.stalk (f y))) 0).obj M))) := by
  intro F
  let Z : RingedSpace.{u} :=
    { carrier := X.carrier
      presheaf := (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).obj
      IsSheaf := (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).property }
  let k := TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} f.base Y.presheaf y ≫
    (TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map
      (toSheafify (Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pullback CommRingCat.{u} f.base).obj Y.presheaf))
  have : IsIso (TopCat.Presheaf.stalkPullbackHom CommRingCat.{u}
      f.base Y.presheaf y) :=
    (TopCat.Presheaf.stalkPullbackIso CommRingCat.{u} f.base Y.presheaf y).isIso_hom
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y CommRingCat.{u}
    ((TopCat.Presheaf.pullback CommRingCat.{u} f.base).obj Y.presheaf)
  have : IsIso k := inferInstance
  let := RingedSpace.moduleStalkFunctor_preservesZeroMorphisms Z y
  have : PreservesFiniteLimits (RingedSpace.moduleStalkFunctor Z y) :=
    stalk_preservesFiniteLimits Z y
  have : PreservesFiniteColimits (RingedSpace.moduleStalkFunctor Z y) :=
    stalk_preservesFiniteColimits Z y
  have : (RingedSpace.moduleStalkFunctor Z y).Additive :=
    Functor.additive_of_preserves_binary_products _
  let S := RingedSpace.moduleStalkFunctor Z y ⋙ ModuleCat.restrictScalars k.hom
  let Sc := S.mapHomologicalComplex (.up ℤ)
  let : QuasiIso q := hq
  have : S.PreservesHomology := inferInstance
  have : QuasiIso (Sc.map q) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology q S
  let a := asIso (DerivedCategory.Q.map (Sc.map q))
  obtain ⟨b⟩ := relative_inverseImage_stalk_restriction_iso f y K
  let c := a ≪≫ DerivedCategory.Q.mapIso b
  refine ⟨S.obj F, fun i ↦ ?_⟩
  obtain ⟨d⟩ := stalk_kFlat_tensor_homology_iso Z y
    (Y.presheaf.stalk (f y)) (asIso k) P hP F i
  exact ⟨d ≪≫ (forget₂ (ModuleCat.{u} (Y.presheaf.stalk (f y)))
    AddCommGrpCat.{u}).mapIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Y.presheaf.stalk (f y))) i).mapIso
        (tensorIso c (Iso.refl ((DerivedCategory.singleFunctor
          (ModuleCat.{u} (Y.presheaf.stalk (f y))) 0).obj (S.obj F)))))⟩

end AlgebraicGeometry.Scheme
