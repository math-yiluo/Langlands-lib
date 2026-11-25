/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.HomComplexSingle
import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- In negative degree both sides of the Ext-sheaf comparison are zero.
No regularity or rank hypothesis is needed for this vanishing statement.

Source: Stacks Project, Cohomology on Sites, Section 08J7 (derived sheaf Hom),
and Duality for Schemes, Tag 0BQZ (negative degrees of the comparison).
(blueprint: lem-sc-koszul-regular-immersion-ext-sheaf-negative).

Proof: resolve the target structure sheaf by its ordinary injective resolution,
extended by zero to integer degrees. This complex is zero in negative degrees
and is K-injective. The representative comparison for derived internal Hom
computes RHom by Hom-complex from the pushforward structure sheaf in degree zero.
By homComplex_single_iso this is degreewise ordinary internal Hom into the
resolution. Internal Hom is additive in the target, so these terms are zero in
negative degrees. Hence its negative homology is zero. The specified locally
ranked exterior term is definitionally zero for q < 0, and pushforward preserves
zero objects. The unique isomorphism between these zero objects gives the result.
This also applies to the empty source and rank zero. -/
theorem koszulRegularImmersion_extSheaf_negative
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (r : LocallyConstant Z ℕ)
    {q : ℤ} (hq : q < 0) :
    Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) q).obj
        ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                (SheafOfModules.unit Y.ringCatSheaf))) ≅
      (Scheme.Modules.pushforward i).obj
        (Scheme.Modules.locallyRankedExteriorTerm
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf)) r q)) := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let P : A := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let L : A := SheafOfModules.unit Y.ringCatSheaf
  let Pc := (CochainComplex.singleFunctor A 0).obj P
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I := injectiveResolution L
  have : I.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective I.cochainComplex 0
  obtain ⟨e⟩ := derivedInternalHom_obj_iso
    (Opens.grothendieckTopology Y) Y.sheaf
    ((DerivedCategory.singleFunctor A 0).obj P)
    ((DerivedCategory.singleFunctor A 0).obj L) Pc I.cochainComplex
    (Iso.refl _) ((asIso (DerivedCategory.Q.map I.ι')).symm)
  obtain ⟨h⟩ := homComplex_single_iso Y P I.cochainComplex
  let T := (SheafOfModules.homFunctor Y.sheaf).obj (op P)
  let K : CochainComplex A ℤ := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex
  have hK : K.IsStrictlyGE 0 := by infer_instance
  have hz : IsZero ((DerivedCategory.homologyFunctor A q).obj
      ((derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf).obj
        (op ((DerivedCategory.singleFunctor A 0).obj P),
          (DerivedCategory.singleFunctor A 0).obj L))) :=
    (DerivedCategory.isZero_of_isGE (DerivedCategory.Q.obj K) 0 q hq).of_iso
      ((DerivedCategory.homologyFunctor A q).mapIso (e ≪≫ DerivedCategory.Q.mapIso h))
  refine ⟨hz.iso ?_⟩
  rw [Scheme.Modules.locallyRankedExteriorTerm, ite_eq_right (not_le.mpr hq)]
  exact (Scheme.Modules.pushforward i).map_isZero (isZero_zero _)



end AlgebraicGeometry
