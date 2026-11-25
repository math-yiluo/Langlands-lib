/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackage
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Projection-formula arrows and their specified finite-total inverse

Source: Weil conjectures blueprint, proper base change, definition 1264
(blueprint: def-weil-pbc-projection-formula-arrows).
-/

@[expose] public section

universe u v u' v' w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B]
  (L : A ⥤ B) (V : B ⥤ A) [L.Additive] [V.Additive] (adj : L ⊣ V)
  (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)

/-- The chain mate whose degree maps are the sums of the ordinary t_{I^a,F^r}.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def tensorAdjunctionTotal
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (I : CochainComplex B ℤ) (F : CochainComplex A ℤ) :
    CochainComplex.mapBifunctor ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      F (curriedTensor A) ⟶
    (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mapBifunctor I ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
        (curriedTensor B)) := by
  letI := tensorPullbackTotal_isIso L e he V adj
    ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) F
  exact (adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv _ _
    (inv (tensorPullbackTotal L e he
      ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) F) ≫
        HomologicalComplex.mapBifunctorMap
          ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I)
          (𝟙 ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj F))
          (curriedTensor B) (ComplexShape.up ℤ))

omit [Abelian A] [Abelian B] [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts A] [HasCoproducts B] [L.Additive] [V.Additive] in
set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] tensorAdjunctionTotal

end CategoryTheory

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]

/-- The uncurried presentation of the existing right-adjoint projection map.
This only transports the bifunctor interface; the mate itself is the upstream
`CategoryTheory.Adjunction.rightAdjointProjectionMap`.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def derivedProjectionFormulaMate
    (L : A ⥤ B) (V : B ⥤ A) (adj : L ⊣ V)
    (TR : A × A ⥤ A) (TS : B × B ⥤ B)
    (alpha : TR ⋙ L ≅ (L.prod L) ⋙ TS) (E : B) (F : A) :
    TR.obj (V.obj E, F) ⟶ V.obj (TS.obj (E, L.obj F)) :=
  ((adj.rightAdjointProjectionMap (T_C := Functor.curry.obj TS)
    (T_D := Functor.curry.obj TR)
    (Functor.curry.map alpha.hom ≫ (Functor.curryObjProdComp L L TS).hom)).app E).app F

end CategoryTheory

attribute [local irreducible] HomologicalComplex₂.total HomologicalComplex.mapBifunctorMap

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency true

set_option synthInstance.maxSize 2048

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
  (PR : ObjectProperty (CochainComplex (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ))
  (hPR : ∀ P, PR P ↔ P.IsKFlatTensor ∧ ∀ n : ℤ, (P.X n).IsFlat)
  (TR : DerivedCategory (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) × DerivedCategory (SheafOfModules.{u} ((sheafCompose J (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
  (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
    ((@curriedTensor (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) _ (monoidalCategory R)).map₂HomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
        ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)

end SheafOfModules

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

end SheafOfModules
