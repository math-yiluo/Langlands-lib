/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction

/-!
# Constructions on a compatible pro-etale compactification tower

The two sides below are independently constructed: the canonical origin compositor,
conjugated to the supplied candidates by canonical comparisons, and the open adjunct of
inverse ordinary exchange followed by the direct-image and open-extension compositors.

## References

* Stacks Tags 0F7B and 0F7J
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Ordinary derived direct image P on the small pro-etale site. -/
abbrev towerP {X Y : Scheme.{u}} (t : X ⟶ Y) :=
  (lowerStar (ModuleCat.{u + 1} Λ) t).rightDerivedFunctor

/-- Exact derived extension by zero J on the small pro-etale site. -/
abbrev towerJ {X Y : Scheme.{u}} (v : X ⟶ Y) [IsOpenImmersion v] :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) v).mapDerivedCategory

/-- Exact derived restriction along a scheme map. -/
abbrev towerPull {X Y : Scheme.{u}} (v : X ⟶ Y) :=
  (upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategory

/-- Exact inverse image is left adjoint to total direct image. -/
def towerPullPushAdjunction {X Y : Scheme.{u}} (v : X ⟶ Y) :
    towerPull Λ v ⊣ towerP Λ v :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).ofNatIsoLeft
    (Functor.leftDerivedFunctorIsoMapDerivedCategory _)

/-- Canonical pullback comparison of the commutative square, descended termwise. -/
def towerPullSquare {H T V S : Scheme.{u}} (b : H ⟶ T) (i : V ⟶ S)
    (r : H ⟶ V) (p : T ⟶ S) (w : b ≫ p = r ≫ i) :
    towerPull Λ i ⋙ towerPull Λ r ≅ towerPull Λ p ⋙ towerPull Λ b :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      ((upperStarComp (ModuleCat.{u + 1} Λ) r i).symm ≪≫
        eqToIso (congrArg (upperStar (ModuleCat.{u + 1} Λ)) w.symm) ≪≫
        upperStarComp (ModuleCat.{u + 1} Λ) b p) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The actual ambient exchange Ex^p: unit for r, square, counit for p. -/
def towerExchange {H T V S : Scheme.{u}} (b : H ⟶ T) (i : V ⟶ S)
    (r : H ⟶ V) (p : T ⟶ S) (w : b ≫ p = r ≫ i)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))) :
    (towerPull Λ i).obj ((towerP Λ p).obj K) ⟶
      (towerP Λ r).obj ((towerPull Λ b).obj K) :=
  (towerPullPushAdjunction Λ r).unit.app _ ≫
    (towerP Λ r).map ((towerPullSquare Λ b i r p w).hom.app _ ≫
      (towerPull Λ b).map ((towerPullPushAdjunction Λ p).counit.app K))

/-- The open unit eta_b, induced from the actual sheaf adjunction unit. -/
def towerOpenUnit {X Y : Scheme.{u}} (b : X ⟶ Y) [IsOpenImmersion b] :
    𝟭 _ ≅ towerJ Λ b ⋙ towerPull Λ b :=
  (Functor.mapDerivedCategoryIdIso _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (asIso (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) b).unit) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Lambda is Ex^p on J_b N followed by P_r of inverse eta_b. -/
def towerLambda {H T V S : Scheme.{u}} (b : H ⟶ T) (i : V ⟶ S)
    (r : H ⟶ V) (p : T ⟶ S) [IsOpenImmersion b]
    (w : b ≫ p = r ≫ i)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology H) (ModuleCat.{u + 1} Λ))) :
    (towerPull Λ i).obj ((towerP Λ p).obj ((towerJ Λ b).obj N)) ⟶
      (towerP Λ r).obj N :=
  towerExchange Λ b i r p w ((towerJ Λ b).obj N) ≫
    (towerP Λ r).map ((towerOpenUnit Λ b).inv.app N)

/-- The map `J_i (P_r N) ⟶ P_p (J_b N)` corresponding, under the Hom bijection, to the
inverse of the invertible map `towerLambda`. -/
def towerGamma {H T V S : Scheme.{u}} (b : H ⟶ T) (i : V ⟶ S)
    (r : H ⟶ V) (p : T ⟶ S) [IsOpenImmersion b] [IsOpenImmersion i]
    (w : b ≫ p = r ≫ i)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology H) (ModuleCat.{u + 1} Λ)))
    (hLambda : IsIso (towerLambda Λ b i r p w N)) :
    (towerJ Λ i).obj ((towerP Λ r).obj N) ⟶
      (towerP Λ p).obj ((towerJ Λ b).obj N) :=
  letI := hLambda
  (((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryAdjunction).homEquiv _ _).symm
      (inv (towerLambda Λ b i r p w N))

/-- Canonical change of candidate on the full etale-origin class. Transport the
canonical etale common-refinement comparison through the named site comparisons,
then descend it uniquely along the etale-origin equivalence. This is not a choice
of an arbitrary isomorphism. -/
def towerCandidateComparison [Finite Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] (c d : Compactification f) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ≅
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} Λ) X
  let model := compactSupportSiteComparison Λ c ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso Λ c d)
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory ≪≫
    (compactSupportSiteComparison Λ d).symm
  (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso model

end AlgebraicGeometry.ProEtale
