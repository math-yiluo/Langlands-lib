/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.Order.Category.Preord
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.AlgebraicGeometry.SemilinearGeometryDerived
public import WeilConjectures.AlgebraicGeometry.SemilinearModuleAdjunction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
public import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.ExactDerivedAdjunction
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
public import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
public import WeilConjectures.CategoryTheory.ScalarInverseImageIndependent
public import WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquations
public import WeilConjectures.SecSmoothPurity.CochainInverseComparison
public import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherence
/-!
# Interfaces for coefficient projection cocycles

Source: Stacks Project, Cohomology on Sites, Tags 07A7 and 0E47; Tags 0D6D,
0D6E and 07A6 for the canonical comparisons and adjunctions
(auxiliary; not a blueprint node).

The auxiliary records present the specified geometric operations, comparison and
unit maps. Ordinary insertion and K-flat computation fix all comparisons; the
cocycle is a conclusion, never part of the input. The same assertion is stated
on the actual vertical sequence sites, before evaluation or derived inverse limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r

open CategoryTheory CategoryTheory.Limits
open SheafOfModules
open scoped ChangeOfRings

namespace SheafOfModules.RingedCoefficientProjection

open WeilConjectures.SemilinearSections (Mod D)

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}

/-- Cache an already inferred sheaf instance on an essentially small site.
Source: Mathlib site transport and sheafification instances. The proof is typeclass inference.
(auxiliary; not a blueprint node). -/
instance (priority := 100000) cachedComposeRings (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := inferInstance

/-- Cache an already inferred sheaf instance on an essentially small site.
Source: Mathlib site transport and sheafification instances. The proof is typeclass inference.
(auxiliary; not a blueprint node). -/
instance (priority := 100000) cachedComposeSets (J : GrothendieckTopology C) :
    J.HasSheafCompose (CategoryTheory.forget CommRingCat.{r}) := inferInstance

/-- Cache an already inferred sheaf instance on an essentially small site.
Source: Mathlib site transport and sheafification instances. The proof is typeclass inference.
(auxiliary; not a blueprint node). -/
instance (priority := 100000) cachedComposeModules (J : GrothendieckTopology C) :
    J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{r}) := inferInstance

/-- The existing underlying set-sheaf functor, used to normalize scalar insertion.
Source: Stacks 03D7 (auxiliary; not a blueprint node). -/
abbrev underlying (R : Sheaf J CommRingCat.{r}) :=
  toSheaf ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})

/-- Presentations of all K-flat derived scalar extensions on this site.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
abbrev Scalars (J : GrothendieckTopology C) :=
  ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    _root_.SheafOfModules.SuccessiveDerivedQuotient.Presentation.{c, v, r, max c v (r + 1)} a

/-- The normalized unit insertion into the recorded ordinary scalar extension.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
def insertion {p : Scalars.{c, v, r} J}
    (n : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r, max c v (r + 1)}
      (J := J) p)
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Mod J R) :
    (underlying R).obj M ⟶ (underlying S).obj ((p a).ordinary.obj M) :=
  (underlying R).map ((n.ordinaryAdjunction a).unit.app M)

/-- The canonical K-flat computation arrow of the recorded universal derived pair.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
abbrev computation {R S : Sheaf J CommRingCat.{r}} {a : R ⟶ S}
    (p : _root_.SheafOfModules.SuccessiveDerivedQuotient.Presentation.{c, v, r, max c v (r + 1)} a)
    (P : CochainComplex (Mod J R) ℤ) :=
  derivedPullbackComplexComparison p.ordinary p.derived p.counit P

/-- A presentation of the geometric inverse images and their actual module adjunctions.
The ring maps and module operations are transported by AlgebraicInverseImage. The
underlying unit fixes the ordinary adjunction; its canonical derived adjunction is
used below. These are presentation witnesses for the operations of the statement.
Source: Stacks 03D7, 07A6 (auxiliary; not a blueprint node). -/
structure Geometry
    (uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r))
    (uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)) (adj : uInv ⊣ uPush) where
  rings : Sheaf J CommRingCat.{r} ⥤ Sheaf K CommRingCat.{r}
  inverse : ∀ R : Sheaf J CommRingCat.{r}, AlgebraicInverseImage uInv R (rings.obj R)
  rings_naturality : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{r})).map a) ≫
        (inverse S).ringUnderlying.hom =
      (inverse R).ringUnderlying.hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{r})).map (rings.map a)
  [inverseAdditive : ∀ R, (inverse R).modules.Additive]
  [inverseLimits : ∀ R, PreservesFiniteLimits (inverse R).modules]
  [inverseColimits : ∀ R, PreservesFiniteColimits (inverse R).modules]
  push : ∀ R : Sheaf J CommRingCat.{r}, Mod K (rings.obj R) ⥤ Mod J R
  [pushAdditive : ∀ R, (push R).Additive]
  [kInjective : ∀ R : Sheaf J CommRingCat.{r},
    Abelian.HasKInjectiveResolutions (Mod K (rings.obj R))]
  ordinaryAdjunction : ∀ R, (inverse R).modules ⊣ push R
  pushUnderlying : ∀ R,
    push R ⋙ underlying R ≅ underlying (rings.obj R) ⋙ uPush
  unit_underlying : ∀ (R : Sheaf J CommRingCat.{r}) (M : Mod J R),
    (underlying R).map ((ordinaryAdjunction R).unit.app M) ≫
        (pushUnderlying R).hom.app ((inverse R).modules.obj M) ≫
        uPush.map ((inverse R).moduleUnderlying.hom.app M) =
      adj.unit.app ((underlying R).obj M)

attribute [instance] Geometry.inverseAdditive Geometry.inverseLimits Geometry.inverseColimits
  Geometry.pushAdditive Geometry.kInjective

variable {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)

/-- Exact coefficient inverse image on ordinary unbounded derived categories.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
abbrev Geometry.left (R : Sheaf J CommRingCat.{r}) := (g.inverse R).modules.mapDerivedCategory

variable {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r, max c v (r + 1)}
      (J := J) pY)
  (nX : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r, max c v (r + 1)}
      (J := K) pX)

/-- The canonical inverse-image/scalar comparison. The ordinary insertion equation
fixes the inverse-image tensor map. Its derived comparison is fixed on common
flat-term K-flat representatives by the universal computation arrows.
Source: Stacks 0D6D, 0G7E (auxiliary; not a blueprint node). -/
structure Comparisons where
  ordinary : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    (pY a).ordinary ⋙ (g.inverse S).modules ≅
      (g.inverse R).modules ⋙ (pX (g.rings.map a)).ordinary
  ordinary_insertion : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Mod J R),
    uInv.map (insertion nY a M) ≫
        (g.inverse S).moduleUnderlying.inv.app ((pY a).ordinary.obj M) ≫
        (underlying (g.rings.obj S)).map ((ordinary a).hom.app M) =
      (g.inverse R).moduleUnderlying.inv.app M ≫
        insertion nX (g.rings.map a) ((g.inverse R).modules.obj M)
  derived : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    (pY a).derived ⋙ g.left S ≅ g.left R ⋙ (pX (g.rings.map a)).derived
  representative : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Mod J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    (∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) →
    (derived a).hom.app (DerivedCategory.Q.obj P) ≫
        (pX (g.rings.map a)).derived.map
          ((g.inverse R).modules.mapDerivedCategoryFactors.hom.app P) ≫
        computation (pX (g.rings.map a))
          (((g.inverse R).modules.mapHomologicalComplex (.up ℤ)).obj P) =
      (g.left S).map (computation (pY a) P) ≫
        (g.inverse S).modules.mapDerivedCategoryFactors.hom.app
          (((pY a).ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (ordinary a).hom (.up ℤ)).app P)

variable (e : Comparisons g nY nX)

end SheafOfModules.RingedCoefficientProjection
