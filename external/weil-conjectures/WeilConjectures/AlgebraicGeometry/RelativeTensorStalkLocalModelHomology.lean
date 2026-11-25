/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.AlgebraicGeometry.RelativeTensorStalkGlobalHomology
import WeilConjectures.AlgebraicGeometry.RelativeTensorGlobalLocalStalkDerivedIso
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Relative tensor homology compared with a local stalk model

Source: Stacks Project, Cohomology of Sheaves, Tags 06YB, 08CG and 09U9;
Modules, Tag 01AG; Tag 0B6G, condition (3).
(blueprint: lem-pc-relative-tensor-stalk-local-model-homology).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- The tensor of a prescribed K-flat representative computes derived tensor of
any local stalk model, without boundedness, projectivity or Tor assumptions.

Source: Stacks Project, Cohomology of Sheaves, Tags 06YB, 08CG and 09U9;
Modules, Tag 01AG; Tag 0B6G, condition (3).
(blueprint: lem-pc-relative-tensor-stalk-local-model-homology).

Proof: take the stalk of the inverse-image ring sheaf at y. Its canonical ring
isomorphism with the target structure stalk at f(y) transports the stalk of F
to an A-module M, where A is that target structure stalk. Stalks preserve
homology and commute with total tensor and the degree-zero single complex.
The stalk criterion makes the transported stalk complex of P K-flat. The
quasi-isomorphism q, exactness of scalar restriction and stalks, and the local
derived isomorphism eL identify its derived object with the scalar-restricted
stalk complex of L. Here hy gives cofinality of the neighbourhoods inside V,
and the open-immersion stalk ring isomorphism is precisely the scalar transport
used by openModuleStalkFunctor. Tensor the derived isomorphism with M[0].
K-flat tensor computation identifies its left side with the stalk of the tensor
complex. Apply degree-i homology and forget scalar structure to obtain the
claimed isomorphism of abelian groups. These constructions use the same M in
all degrees. No representative is chosen from a mere existence theorem to
define data: M is the actual stalk of F transported by a ring isomorphism. -/
theorem relativeTensor_stalk_localModel_homology_iso
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
                        (((openModuleStalkFunctor X V ⟨y, hy⟩).mapHomologicalComplex
                          (.up ℤ)).obj L)) ⊗
                    (DerivedCategory.singleFunctor
                      (ModuleCat.{u} (Y.presheaf.stalk (f y))) 0).obj M))) := by
  intro F
  obtain ⟨M, hM⟩ := relativeTensor_stalk_global_homology_iso f K y P hP q hq F
  obtain ⟨e⟩ := relativeTensor_global_local_stalk_derived_iso f K V L eL y hy
  refine ⟨M, fun i ↦ ?_⟩
  obtain ⟨a⟩ := hM i
  exact ⟨a ≪≫ (forget₂ (ModuleCat.{u} (Y.presheaf.stalk (f y)))
    AddCommGrpCat.{u}).mapIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Y.presheaf.stalk (f y))) i).mapIso
        (tensorIso e (Iso.refl ((DerivedCategory.singleFunctor
          (ModuleCat.{u} (Y.presheaf.stalk (f y))) 0).obj M))))⟩

end AlgebraicGeometry.Scheme
