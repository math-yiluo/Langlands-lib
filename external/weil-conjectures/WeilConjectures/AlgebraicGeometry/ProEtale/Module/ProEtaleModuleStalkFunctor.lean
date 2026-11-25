/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantSheafStalk
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Functorial module stalks on the pro-etale site

The objects and scalar action are the recorded module colimit construction;
this interface retains the induced maps and additivity needed for complexes.

## References

* Stacks Project, Tags 0F6B and 002F
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- The module-valued pointed-neighbourhood colimit, including its action on maps. -/
noncomputable def geometricRingModuleStalkFunctor (y : Spec (.of Ω) ⟶ Y)
    (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O) ⥤
        ModuleCat.{u + 1} (proEtaleGeometricStalkRing y O) :=
  SheafOfModules.forget _ ⋙
    PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget y)
      (O.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
    PresheafOfModules.colimitFunctor
      (colimit.isColimit (proEtaleGeometricStalkRingDiagram y O))

/-- Additivity of the canonical module stalk. -/
theorem geometricRingModuleStalkFunctor_additive (y : Spec (.of Ω) ⟶ Y)
    (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    (geometricRingModuleStalkFunctor y O).Additive := by
  have : (PresheafOfModules.constFunctor
      (colimit.cocone (proEtaleGeometricStalkRingDiagram y O))).Additive := by
    constructor
    intro M N f g
    ext X
    rfl
  have : (PresheafOfModules.colimitFunctor
      (colimit.isColimit (proEtaleGeometricStalkRingDiagram y O))).Additive :=
    (PresheafOfModules.colimitAdjunction
      (colimit.isColimit (proEtaleGeometricStalkRingDiagram y O))).left_adjoint_additive
  have : (PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget y)
      (O.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).Additive := by
    constructor
    intro M N f g
    ext X
    rfl
  unfold geometricRingModuleStalkFunctor
  infer_instance

attribute [instance] geometricRingModuleStalkFunctor_additive

/-- The finite-coefficient stalk with scalars restricted along the actual constant germ. -/
noncomputable def finiteCoefficientModuleStalkFunctor (y : Spec (.of Ω) ⟶ Y)
    (A : Type u) [CommRing A] :
    SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1, u} A) :=
  geometricRingModuleStalkFunctor y _ ⋙
    ModuleCat.restrictScalars (proEtaleConstantRingGerm y A)

/-- Additivity follows from the two additive factors of the stalk functor. -/
noncomputable instance finiteCoefficientModuleStalkFunctorAdditive
    (y : Spec (.of Ω) ⟶ Y) (A : Type u) [CommRing A] :
    (finiteCoefficientModuleStalkFunctor y A).Additive :=
  inferInstanceAs ((geometricRingModuleStalkFunctor y _ ⋙
    ModuleCat.restrictScalars (proEtaleConstantRingGerm y A)).Additive)

end AlgebraicGeometry.Scheme
