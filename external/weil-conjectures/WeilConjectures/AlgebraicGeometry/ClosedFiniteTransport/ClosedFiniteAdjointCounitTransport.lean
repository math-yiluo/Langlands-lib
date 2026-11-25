/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportTriangle
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Closed finite exceptional inverse image and its counit

Source: blueprint main-20261015, sk-prop-a1, first localization triangle;
Stacks Project, Tags 04CA, 015F, 09A6 and 09BM
(blueprint: lem-pur-closed-finite-adjoint-counit-transport).

The auxiliary definitions are the specified canonical identifications, not additional
choices of functors or adjunctions. The support adjoint is exactly the one used by
`exists_etale_closedSupportTriangle`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits WeilConjectures

namespace AlgebraicGeometry.ProEtale.ClosedFiniteTransport

/-- Finiteness of the coefficient quotient in the purity conventions.
Source: finite coefficient datum, sk-def-purity-conv
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
instance coefficientFinite (P : PurityFiniteSetting.{u}) : Finite P.Coefficient :=
  haveI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {Z X U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The existing etale compact-support left-adjoint theorem at the identity compactification.
Source: sk-prop-a1 and the ordinary exceptional adjoint
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
instance compactSupportIsLeftAdjoint :
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (Compactification.ofIsProper i)).IsLeftAdjoint :=
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A
    (Compactification.ofIsProper i)

/-- The canonical identity/proper compactification comparison, on all unbounded objects.
Source: sk-prop-a1, first localization triangle; identity extension by zero, Tag 03S3
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
def compactSupportIso :
    Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (Compactification.ofIsProper i) ≅
      (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor :=
  Functor.isoWhiskerRight
    (Etale.mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) Z) _ ≪≫
    Functor.leftUnitor _

/-- The second canonical identification with termwise closed direct image.
Source: Stacks Tags 04CA and 015F, exact closed pushforward
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
def termwiseIso :
    (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor ≅
      (Etale.lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory :=
  (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorIsoMapDerivedCategory

variable (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
variable (hij : IsCompl (Set.range i.base) (Set.range j.base))

/-- Termwise pro-etale closed direct image, with exactness supplied by the complement.
Source: Stacks Tag 09BM (blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
def proTermwise :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  haveI := preservesFiniteColimits_lowerStar_of_isCompl (R := A) i j hij
  (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory

/-- The specified closed comparison: descend the underived direct-image comparison
termwise and identify the exact etale derived direct image with its termwise descent.
Source: Stacks Tags 09A6 and 09BM
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
def closedComparison :
    (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory ⋙
        proTermwise A i j hij :=
  haveI := preservesFiniteColimits_lowerStar_of_isCompl (R := A) i j hij
  haveI := isIso_lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)
  Functor.isoWhiskerRight (termwiseIso A i) _ ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (asIso (lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A))) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The transported counit obtained by expanding the finite etale-origin Hom bijections.
It uses the comparison inverse, the transported ordinary etale counit, and the actual
comparison-adjunction counit in that order; it asserts no ambient pro-etale adjunction.
Source: sk-prop-a1, first localization triangle; sk-def-sf-operations (vi)
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
def transportedCounit
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (proTermwise A i j hij).obj
        ((sfFiniteExceptionalAt A (Compactification.ofIsProper i)).obj K) ⟶ K :=
  (closedComparison A i j hij).inv.app _ ≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
      (((Adjunction.ofIsLeftAdjoint
        (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) (Compactification.ofIsProper i))).ofNatIsoLeft
          (compactSupportIso A i)).counit.app _) ≫
    (derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).counit.app K

/-- The inverse used in the classical-input comparison is the inverse of the actual unit.
Source: Bhatt--Scholze, Proposition 5.2.6; sk-prop-a1
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
def comparisonUnitIso (T : Scheme.{u})
    (B : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    B.obj ≅ ((comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctor).obj
      (((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory).obj B.obj) :=
  haveI := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} A) T B.obj B.property
  asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app B.obj)

end AlgebraicGeometry.ProEtale.ClosedFiniteTransport
