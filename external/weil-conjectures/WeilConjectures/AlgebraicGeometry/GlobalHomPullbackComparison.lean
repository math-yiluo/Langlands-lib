/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom


/-! # Canonical pullback comparison on global derived Hom
Source: Stacks Project, Cohomology, Remark 08I3 and Section 0B6A;
Duality, Tag 0AA8 (blueprint: def-pc-global-hom-pullback-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe uP wP
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{uP},
  HasDerivedCategory.{wP} (SheafOfModules.{uP} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type uP) [Ring R], HasDerivedCategory.{wP} (ModuleCat.{uP} R)]

/-- Apply global sections to the evaluation-mate pullback map, then the canonical
Leray comparison. No comparison map is supplied as an input.
Source: Stacks, Tags 08I3, 0B6A and 0AA8
(blueprint: def-pc-global-hom-pullback-comparison). -/
def schemeGlobalDerivedHom_pullback_comparison
    {S T : Scheme.{uP}} (h : T ⟶ S) (P Q : schemeDerivedCategory S) :
    (schemeGlobalDerivedHom S).obj (op P, Q) ⟶
      (schemeGlobalScalarRestriction h).obj
        ((schemeGlobalDerivedHom T).obj
          (op ((derivedPullback h).obj P), (derivedPullback h).obj Q)) :=
  (schemeDerivedGlobalSections S).map
      ((schemeHomPullbackAdjunction h).homEquiv _ _
        (((schemeDerivedTensorHomEquiv T)
          ((derivedPullback h).obj
            ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q)))
          ((derivedPullback h).obj P) ((derivedPullback h).obj Q)).symm
            ((mixedHomTensorPullbackIso h).inv.app
              ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q), P) ≫
              (derivedPullback h).map
                ((schemeDerivedTensorHomEquiv S)
                  ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q))
                  P Q (𝟙 _))))) ≫
    (mixedGlobalSectionsDirectImageIso h).hom.app
      ((derivedInternalHom (Opens.grothendieckTopology T) T.sheaf).obj
        (op ((derivedPullback h).obj P), (derivedPullback h).obj Q))

/-- Restriction of scalars along a composite, with the identity module comparison.
Source: Stacks, Tags 0B6A and 0AA8
(blueprint: def-pc-global-hom-pullback-comparison). -/
def schemeGlobalScalarRestrictionCompIso {X Y Z : Scheme.{uP}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    schemeGlobalScalarRestriction (f ≫ g) ≅
      schemeGlobalScalarRestriction f ⋙ schemeGlobalScalarRestriction g :=
  Functor.mapDerivedCategoryNatIso
    (ModuleCat.restrictScalarsComp' g.appTop.hom f.appTop.hom (f ≫ g).appTop.hom rfl) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Scalar identification of the two paths around a commutative square.
Source: Stacks, Tags 0B6A and 0AA8
(blueprint: def-pc-global-hom-pullback-comparison). -/
def schemeGlobalScalarSquareIso {X Y X' Y' : Scheme.{uP}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (gX : X' ⟶ X)
    (h : gX ≫ f = f' ≫ g) :
    schemeGlobalScalarRestriction gX ⋙ schemeGlobalScalarRestriction f ≅
      schemeGlobalScalarRestriction f' ⋙ schemeGlobalScalarRestriction g :=
  (schemeGlobalScalarRestrictionCompIso gX f).symm ≪≫
    eqToIso (congrArg schemeGlobalScalarRestriction h) ≪≫
      schemeGlobalScalarRestrictionCompIso f' g

end AlgebraicGeometry
