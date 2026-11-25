/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# The specified boundary exceptional Hom transport

Source: Stacks Project, Tags 0B65 and 0DV0; blueprint boundary-duality discharge,
ordinary-to-pro-etale realization
(blueprint: def-weil-boundary-exceptional-comparison-data).

## Main definitions

- `homTransport`: the specified four-stage Hom transport.
- `exceptionalOriginMap`: the comparison-unit identification at an etale-origin object.
- `CounitComparison`: the corresponding transported-counit compatibility property.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.BoundaryComparison

/-- The existing constant scalar-module coefficient category, at the established site size.
Source: blueprint ordinary module categories; Stacks 07A4
(blueprint: def-weil-boundary-exceptional-comparison-data). -/
abbrev coefficients (A : Type u) [CommRing A] :=
  ModuleCat.{u + 1} (ULift.{u + 1, u} A)

/-- Exact comparison on the ordinary derived categories. Source: Stacks 099R;
(blueprint: def-weil-boundary-exceptional-comparison-data). -/
abbrev comparison (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] (T : Scheme.{u}) :=
  (comparisonUpperStar C T).mapDerivedCategory

/-- Ordinary etale direct image. Source: Stacks 07A6;
(blueprint: def-weil-boundary-exceptional-comparison-data). -/
abbrev etaleImage (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] {Z T : Scheme.{u}} (i : Z ⟶ T) :=
  (Etale.lowerStar C i).rightDerivedFunctor

/-- Ordinary pro-etale direct image. Source: Stacks 07A6;
(blueprint: def-weil-boundary-exceptional-comparison-data). -/
abbrev proetaleImage (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] {Z T : Scheme.{u}} (i : Z ⟶ T) :=
  (lowerStar C i).rightDerivedFunctor

/-- The canonical pullback square, expressed with exact comparison functors.
Source: Stacks 0E48; (blueprint: def-weil-boundary-exceptional-comparison-data). -/
def pullbackSquare (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {Z T : Scheme.{u}} (i : Z ⟶ T) :
    comparison C T ⋙
        (upperStar C i).leftDerivedFunctor ≅
      (Etale.upperStar C i).leftDerivedFunctor ⋙
        comparison C Z :=
  let P := upperStar C i
  let E := Etale.upperStar C i
  let CT := comparisonUpperStar C T
  let CZ := comparisonUpperStar C Z
  Functor.isoWhiskerLeft (comparison C T) P.leftDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryCompIso CT P ≪≫
    Functor.mapDerivedCategoryNatIso (comparisonUpperStarCompUpperStarIso C i) ≪≫
    (Functor.mapDerivedCategoryCompIso E CZ).symm ≪≫
    Functor.isoWhiskerRight E.leftDerivedFunctorIsoMapDerivedCategory.symm (comparison C Z)

/-- The canonical direct-image mate, with its ordinary counit normalization built in.
Source: Stacks 0B65; (blueprint: def-weil-boundary-exceptional-comparison-data). -/
def directImageMate (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {Z T : Scheme.{u}} (i : Z ⟶ T) :
    etaleImage C i ⋙ comparison C T ⟶ comparison C Z ⋙ proetaleImage C i :=
  mateEquiv
    (Etale.derivedUpperStarLowerStarAdjunction
      C i)
    (derivedUpperStarLowerStarAdjunction
      C i)
    (pullbackSquare C i).hom

/-- The recorded etale exceptional inverse image with the identity-open compactification.
Source: blueprint finite exceptional inverse image;
(blueprint: def-weil-boundary-exceptional-comparison-data). -/
abbrev etaleExceptional (A : Type u) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i] :=
  letI := (Compactification.ofIsProper i).hasCompactification
  Etale.rightDerivedUpperShriek (ULift.{u + 1, u} A) i

/-- Its actual adjunction, normalized by the identity-open support comparison.
Source: blueprint ordinary exceptional adjunction; Stacks 0B65
(blueprint: def-weil-boundary-exceptional-comparison-data). -/
def exceptionalAdjunction (A : Type u) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i] :
    etaleImage (coefficients A) i ⊣ etaleExceptional A i :=
  letI := (Compactification.ofIsProper i).hasCompactification
  (Etale.rightDerivedUpperShriekAdjunction
    (ULift.{u + 1, u} A) i).ofNatIsoLeft
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
        (coefficients A) i)

/-- The finite exceptional formula, in fixed constant coefficients. Its factors are the
existing derived functors; only the identity-open compactification instance is installed.
Source: blueprint finite exceptional inverse image
(blueprint: def-weil-boundary-exceptional-comparison-data). -/
abbrev proetaleExceptional (A : Type u) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i] :=
  sfFiniteExceptionalFixed A (Compactification.ofIsProper i)

/-- The specified Hom transport: precompose with b, use the comparison adjunction, use
ordinary exceptional adjunction, then apply C_Z to the resulting morphism.
Source: Stacks 0DV0 and 0B65; blueprint displayed Hom chain
(blueprint: def-weil-boundary-exceptional-comparison-data). -/
def homTransport (A : Type u) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i]
    (H : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (coefficients A)))
    (L : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (coefficients A)))
    (f : (proetaleImage (coefficients A) i).obj
      ((comparison (coefficients A) Z).obj H.obj) ⟶ L.obj) :
    (comparison (coefficients A) Z).obj H.obj ⟶
      (proetaleExceptional A i).obj L.obj :=
  (comparison (coefficients A) Z).map
    ((exceptionalAdjunction A i).homEquiv _ _
      ((derivedComparisonAdjunction
        (coefficients A) T).homEquiv _ _
        ((directImageMate (coefficients A) i).app H.obj ≫ f)))

/-- The etale exceptional value retains its bounded-below typing from the existing
finite-coefficient interface. Source: blueprint finite exceptional inverse image
(blueprint: def-weil-boundary-exceptional-comparison-data). -/
def exceptionalPlus (A : Type u) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i] [CompactSpace T]
    (N : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (coefficients A))) :
    DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (coefficients A)) :=
  letI := (Compactification.ofIsProper i).hasCompactification
  ⟨(etaleExceptional A i).obj N.obj,
    Etale.plus_rightDerivedUpperShriek_obj
      (ULift.{u + 1, u} A) i N.obj N.property⟩

/-- The identification C_Z G_e N -> G_p C_T N induced by the actual comparison unit.
Source: blueprint displayed Hom chain; Stacks 0DV0
(blueprint: def-weil-boundary-exceptional-comparison-data). -/
def exceptionalOriginMap (A : Type u) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i]
    (N : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (coefficients A))) :
    (comparison (coefficients A) Z).obj ((etaleExceptional A i).obj N.obj) ⟶
      (proetaleExceptional A i).obj ((comparison (coefficients A) T).obj N.obj) :=
  (comparison (coefficients A) Z).map ((etaleExceptional A i).map
    ((derivedComparisonAdjunction
      (coefficients A) T).unit.app N.obj))

/-- The transported exceptional counit is the uniquely specified preimage of the identity,
written using its etale-origin representative. The identification is exactly the origin-unit
map, and eta is exactly the inverse of the fixed canonical mate.
Source: Stacks 0B65 and 0DV0; blueprint counit formula
(blueprint: def-weil-boundary-exceptional-comparison-data). -/
def CounitComparison (A : Type u) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i] [CompactSpace T]
    (N : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (coefficients A))) : Prop :=
  IsIso (exceptionalOriginMap A i N) ∧
  ∃ b : (comparison (coefficients A) T).obj
        ((etaleImage (coefficients A) i).obj (exceptionalPlus A i N).obj) ≅
      (proetaleImage (coefficients A) i).obj
        ((comparison (coefficients A) Z).obj (exceptionalPlus A i N).obj),
    b.hom = (directImageMate (coefficients A) i).app (exceptionalPlus A i N).obj ∧
    ∃ μ : (proetaleImage (coefficients A) i).obj
        ((comparison (coefficients A) Z).obj (exceptionalPlus A i N).obj) ⟶
        (comparison (coefficients A) T).obj N.obj,
      homTransport A i (exceptionalPlus A i N)
        ((siteComparisonDerivedPullbackPlus T (ULift.{u + 1, u} A)).obj N) μ =
          exceptionalOriginMap A i N ∧
      μ = b.inv ≫ (comparison (coefficients A) T).map ((exceptionalAdjunction A i).counit.app N.obj)

end AlgebraicGeometry.ProEtale.BoundaryComparison
