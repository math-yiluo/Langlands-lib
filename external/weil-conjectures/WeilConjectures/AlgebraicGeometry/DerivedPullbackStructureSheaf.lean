/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits MonoidalCategory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Derived pullback preserves the degree-zero structure sheaf.
Source: Stacks Project, Tags 06YD, 06YJ and 0096.
(blueprint: lem-sc-derived-pullback-structure-sheaf-local).
Proof: the structure sheaf is flat because tensoring with the unit is the identity.
Its degree-zero single complex is bounded above and termwise flat, so the
flat-complex comparison computes derived pullback by termwise tensor pullback.
The single-complex comparisons and the tensor-unit pullback isomorphism identify
the result with the degree-zero structure sheaf on the source. Empty schemes and
zero stalk rings cause no exception to any of these isomorphisms. -/
theorem nonempty_derivedPullback_structureSheaf_iso
    {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    Nonempty ((derivedPullback g).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings S.toRingedSpace))) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings T.toRingedSpace))) := by
  let M := SheafOfModules.unit (moduleRings S.toRingedSpace)
  let n : ℤ := 0
  let A := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings T.toRingedSpace)
  let K := (CochainComplex.singleFunctor A n).obj M
  let := SheafOfModules.monoidalCategory S.sheaf
  obtain ⟨⟨hpreadd⟩, _⟩ := SheafOfModules.tensorClosed S.sheaf
  let := hpreadd
  have hM : SheafOfModules.IsFlat M := by
    change exactFunctor A A (MonoidalCategory.tensorRight (𝟙_ A))
    exact (exactFunctor A A).prop_of_iso (rightUnitorNatIso A).symm
      (by rw [exactFunctor_iff]; exact ⟨inferInstance, inferInstance⟩)
  have hbounded : ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero (K.X q) := by
    refine ⟨n, fun q hq ↦ ?_⟩
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have hflat : ∀ q : ℤ, SheafOfModules.IsFlat (K.X q) := by
    intro q
    by_cases hq : q = n
    · subst q
      let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n M
      exact (exactFunctor _ _).prop_of_iso
        ((MonoidalCategory.curriedTensor A).flip.mapIso e.symm) hM
    · exact (ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)).2
  obtain ⟨F, hF, _, hFadd, _, _, ⟨e, _⟩⟩ :=
    flatComplexDerivedPullback g K hbounded hflat
  let := hFadd
  have hi := (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso g).1
  let eFM : F.obj M ≅ SheafOfModules.unit (moduleRings T.toRingedSpace) :=
    eqToIso (hF M) ≪≫ asIso (Scheme.Modules.tensorPullbackObjUnitToUnit g)
  refine ⟨(derivedPullback g).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ A n).app M ≪≫
      ((DerivedCategory.quotientCompQhIso A).app K).symm) ≪≫ e.symm ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K) ≪≫
    (DerivedCategory.quotientCompQhIso B).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ B n).app (F.obj M)).symm ≪≫
    (DerivedCategory.singleFunctor B n).mapIso eFM⟩

end AlgebraicGeometry
