/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomOriginalCounitNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionNormalization

/-! # Transport of the adjunction to the original derived-pullback counit

Source: Stacks Project, Cohomology, Tag 06YJ; Derived Categories, Tag 09T5.
(blueprint: lem-pc-original-counit-adjunction-transport).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

-- Comparing normalized adjunctions compares the shared localization instances.
/-- The legacy pullback adjunction is the original-counit adjunction transported
back along the unique change of universal counit. This equation records the
necessary transport; the two adjunctions need not be literally equal.

Proof: both adjunctions satisfy the representative Hom equation for the legacy
counit. For the transported original adjunction, the inverse counit-comparison
isomorphism replaces that counit by the original one. Apply uniqueness of normalized
derived adjunctions: their counits coincide after the right-derived unit, and the
absolute right-derived universal property makes the counits equal.
Source: Stacks Project, Cohomology, Tag 06YJ; Derived Categories, Tag 09T5
(blueprint: lem-pc-original-counit-adjunction-transport). -/
theorem schemeHomPullbackAdjunction_eq_original_transport {T S : Scheme.{u}} (g : T ⟶ S) :
    schemeHomPullbackAdjunction g =
      (schemeHomOriginalPullbackAdjunction g).ofNatIsoLeft
        (schemeHomPullbackCounitIso g).symm := by
  let ε := SingleComplexBaseChange.counit.{u, w} g
  let β := (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit
  let b := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g))
    |>.mapHomotopyCategory (.up ℤ)
  let hright : (schemeDerivedDirectImage g ⋙ derivedPullback g).IsRightDerivedFunctor
      (Functor.whiskerRight β (derivedPullback g) ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (.up ℤ)) :=
    (HomotopyCategory.KInjectives.localizerMorphism _)
      |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure β
        (fun I ↦ (HomotopyCategory.KInjectives.localizerMorphism_derives _)
          |>.isIso_of_isRightDerivedFunctor β I) (derivedPullback g)
  let hloc : (DerivedCategory.Qh.{w, u, u + 1}
      (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).IsLocalization
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (.up ℤ)) := inferInstance
  refine @Adjunction.eq_of_normalization _ _ _ _ _ _ _ _ _ _ _ _ b
    (schemeHomPullbackAdjunction g)
    ((schemeHomOriginalPullbackAdjunction g).ofNatIsoLeft
      (schemeHomPullbackCounitIso g).symm)
    (DerivedCategory.Qh.{w, u, u + 1}
      (C := SheafOfModules.{u} (moduleRings S.toRingedSpace)))
    (DerivedCategory.Qh.{w, u, u + 1}
      (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))) ε β
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (.up ℤ)) hloc hright ?_ ?_
  · exact Classical.choose_spec (exists_schemeDerivedAdjunction g
      (hAdd := (Classical.choose exists_derivedPullbackComposition) g)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) g)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) g))
  · intro M K t
    rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
    simp only [Iso.symm_hom, ← Category.assoc]
    dsimp only [ε]
    erw [schemeHomPullbackCounitIso_inv_fac g M]
    exact Classical.choose_spec (exists_schemeDerivedAdjunction g
      (hAdd := SingleComplexBaseChange.tensorPullbackAdditive g)
      (schemeHomPullbackCounitData g).counit
      (schemeHomPullbackCounitData g).isLeftDerived) M K t

end AlgebraicGeometry
