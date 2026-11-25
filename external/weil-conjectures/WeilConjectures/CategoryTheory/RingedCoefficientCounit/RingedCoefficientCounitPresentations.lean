/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# Representative-normalized coefficient counit diagrams

Source: Stacks, Tags 03D7, 07A6 and 0D6E
(blueprint: def-pur-ringed-coefficient-counit-presentations).
Ordinary maps are fixed on sections; derived maps are fixed by localization and
K-flat/K-injective representative equations. No counit identity is a field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r w u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace CategoryTheory.RingedCoefficientCounit

/-- Constant coefficient ring. Source: Stacks 03D7
(blueprint: def-pur-ringed-coefficient-counit-presentations). -/
abbrev constantRing {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{r}] (A : CommRingCat.{r}) :=
  (constantSheaf J CommRingCat.{r}).obj A

/-- The recorded category of module sheaves. Source: Stacks 03D7
(blueprint: def-pur-ringed-coefficient-counit-presentations). -/
abbrev modules {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r})
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] :=
  ringedSiteModules.{r, r, v, u} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- Forget to the sheaf of sets. Source: Stacks 03D7
(blueprint: def-pur-ringed-coefficient-counit-presentations). -/
abbrev underlying {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r})
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.HasSheafCompose (forget AddCommGrpCat.{r})] :=
  SheafOfModules.toSheaf.{r} ((sheafCompose J
    (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⋙ sheafCompose J (forget AddCommGrpCat.{r})

/-- Ordinary restriction of scalars. Source: Stacks 03D7
(blueprint: def-pur-ringed-coefficient-counit-presentations). -/
abbrev restriction {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{r}}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] (a : R ⟶ S) :
    modules S ⥤ modules R :=
  SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map a)

/-- Termwise complex functor. Source: Stacks 07A6
(blueprint: def-pur-ringed-coefficient-counit-presentations). -/
abbrev onComplex {B : Type u₁} [Category.{v₁} B] [Preadditive B]
    {E : Type u₂} [Category.{v₂} E] [Preadditive E] (F : B ⥤ E) [F.Additive] :=
  F.mapHomologicalComplex (ComplexShape.up ℤ)

/-- A canonical derived adjunction, including the representative Hom formula.
Source: Stacks 07A6 and 0FND
(blueprint: def-pur-ringed-coefficient-counit-presentations).
The equation fixes the adjunction itself, rather than only its two adjoint functors. -/
structure DerivedAdjunction
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w} B]
    {E : Type u₂} [Category.{v₂} E] [Abelian E] [HasDerivedCategory.{w} E]
    (L : B ⥤ E) [L.Additive] (R : E ⥤ B) [R.Additive] (a : L ⊣ R) where
  left : DerivedCategory B ⥤ DerivedCategory E
  right : DerivedCategory E ⥤ DerivedCategory B
  epsilon : DerivedCategory.Q ⋙ left ⟶ onComplex L ⋙ DerivedCategory.Q
  eta : onComplex R ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ right
  isLeft : left.IsLeftDerivedFunctor epsilon
    (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))
  isRight : right.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso E (ComplexShape.up ℤ))
  onInjective : ∀ I : CochainComplex E ℤ, I.IsKInjective → IsIso (eta.app I)
  adj : left ⊣ right
  homFormula : ∀ (P : CochainComplex B ℤ) (I : CochainComplex E ℤ),
    I.IsKInjective → ∀ h : P ⟶ (onComplex R).obj I,
      (adj.homEquiv _ _).symm (DerivedCategory.Q.map h ≫ eta.app I) =
        epsilon.app P ≫ DerivedCategory.Q.map
          (((a.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv P I).symm h)

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [UnivLE.{max u v, r}] [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
  [JX.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [JY.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [JX.HasSheafCompose (forget AddCommGrpCat.{r})]
  [JY.HasSheafCompose (forget AddCommGrpCat.{r})]
  [HasSheafify JX AddCommGrpCat.{r}] [JX.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify JY AddCommGrpCat.{r}] [JY.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify JX CommRingCat.{r}] [HasWeakSheafify JY CommRingCat.{r}]
  {A : CommRingCat.{r}} {RX RI : Sheaf JX CommRingCat.{r}}
  {RY : Sheaf JY CommRingCat.{r}}
  {inverse : Sheaf JY (Type r) ⥤ Sheaf JX (Type r)}
  {direct : Sheaf JX (Type r) ⥤ Sheaf JY (Type r)} {geom : inverse ⊣ direct}
  {IA : SheafOfModules.AlgebraicInverseImage inverse (constantRing JY A) (constantRing JX A)}
  {IR : SheafOfModules.AlgebraicInverseImage inverse RY RI} {c : RI ⟶ RX}

/-- Tensor pullback, induced direct images and the scalar-unit comparison.
Source: Stacks 03D7 (blueprint: def-pur-ringed-coefficient-counit-presentations).
Object and morphism equations fix tensor pullback without assuming it exact.
The two Hom equations fix both adjunctions relative to the geometric adjunction.
The scalar-unit formula is the sheafified map `x ↦ 1 ⊗ x`. -/
structure OrdinaryPresentation
    (direct : Sheaf JX (Type r) ⥤ Sheaf JY (Type r)) (geom : inverse ⊣ direct)
    (IA : SheafOfModules.AlgebraicInverseImage inverse
      (constantRing JY A) (constantRing JX A))
    (IR : SheafOfModules.AlgebraicInverseImage inverse RY RI) (c : RI ⟶ RX)
    (aX : constantRing JX A ⟶ RX) (aY : constantRing JY A ⟶ RY)
    (aI : constantRing JX A ⟶ RI) where
  pull : modules RY ⥤ modules RX
  pull_obj : ∀ M, pull.obj M = SheafOfModules.changeOfRings c (IR.modules.obj M)
  pull_map : ∀ {M N} (h : M ⟶ N), pull.map h ≫ eqToHom (pull_obj N) =
    eqToHom (pull_obj M) ≫
      SheafOfModules.changeOfRingsHom c (IR.modules.obj M) (IR.modules.map h)
  pullAdditive : pull.Additive
  inverseAdditive : IA.modules.Additive
  pushR : modules RX ⥤ modules RY
  pushA : modules (constantRing JX A) ⥤ modules (constantRing JY A)
  pushRAdditive : pushR.Additive
  pushAAdditive : pushA.Additive
  pushRUnderlying : pushR ⋙ underlying RY ≅ underlying RX ⋙ direct
  pushAUnderlying : pushA ⋙ underlying (constantRing JY A) ≅
    underlying (constantRing JX A) ⋙ direct
  tensorUnit : ∀ M : modules RY,
    (underlying RI).obj (IR.modules.obj M) ⟶ (underlying RX).obj (pull.obj M)
  tensorUnitFormula : ∀ (M : modules RY) (U : Cᵒᵖ) (x : (IR.modules.obj M).val.obj U),
    (tensorUnit M).hom.app U x = (eqToHom (pull_obj M).symm).val.app U
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose JX (forget₂ CommRingCat.{r} RingCat.{r})).obj RX).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf c (IR.modules.obj M))).app U
            ((1 : RX.obj.obj U) ⊗ₜ[RI.obj.obj U, (c.hom.app U).hom] x))
  adjR : pull ⊣ pushR
  adjA : IA.modules ⊣ pushA
  adjRFormula : ∀ M N (h : pull.obj M ⟶ N),
    (underlying RY).map (adjR.homEquiv M N h) ≫ pushRUnderlying.hom.app N =
      geom.homEquiv _ _
        (IR.moduleUnderlying.inv.app M ≫ tensorUnit M ≫ (underlying RX).map h)
  adjAFormula : ∀ M N (h : IA.modules.obj M ⟶ N),
    (underlying (constantRing JY A)).map (adjA.homEquiv M N h) ≫
        pushAUnderlying.hom.app N =
      geom.homEquiv _ _ (IA.moduleUnderlying.inv.app M ≫
        (underlying (constantRing JX A)).map h)
  inverseRestriction : restriction aY ⋙ IA.modules ≅ IR.modules ⋙ restriction aI
  inverseRestrictionFormula : ∀ M,
    (underlying (constantRing JX A)).map (inverseRestriction.hom.app M) =
      IA.moduleUnderlying.hom.app ((restriction aY).obj M) ≫
        IR.moduleUnderlying.inv.app M
  scalarUnit : restriction aY ⋙ IA.modules ⟶ pull ⋙ restriction aX
  scalarUnitFormula : ∀ M,
    (underlying (constantRing JX A)).map (scalarUnit.app M) =
      (underlying (constantRing JX A)).map (inverseRestriction.hom.app M) ≫ tensorUnit M
  ordinaryKappa : pushR ⋙ restriction aY ≅ restriction aX ⋙ pushA
  ordinaryKappaFormula : ∀ M,
    (underlying (constantRing JY A)).map (ordinaryKappa.hom.app M) ≫
        pushAUnderlying.hom.app ((restriction aX).obj M) = pushRUnderlying.hom.app M

attribute [instance] OrdinaryPresentation.pullAdditive
  OrdinaryPresentation.pushRAdditive OrdinaryPresentation.pushAAdditive

/-- Exactness supplied by the construction, not an extra flatness hypothesis.
Source: Stacks 03D7 and 07A6
(blueprint: def-pur-ringed-coefficient-counit-presentations). -/
structure CoefficientExactness
    (aX : constantRing JX A ⟶ RX) (aY : constantRing JY A ⟶ RY) where
  xLimits : PreservesFiniteLimits (restriction aX)
  xColimits : PreservesFiniteColimits (restriction aX)
  yLimits : PreservesFiniteLimits (restriction aY)
  yColimits : PreservesFiniteColimits (restriction aY)

/-- The canonical derived maps with actual representative normalization equations.
Source: Stacks 03D7, 07A6, 0FND and 0D6E
(blueprint: def-pur-ringed-coefficient-counit-presentations).
The counit square and coefficient naturality are conclusions of the item theorem;
they are deliberately absent from this definition. -/
structure DerivedPresentation
    [IA.modules.Additive]
    {aX : constantRing JX A ⟶ RX} {aY : constantRing JY A ⟶ RY}
    {aI : constantRing JX A ⟶ RI}
    (o : OrdinaryPresentation direct geom IA IR c aX aY aI)
    [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
    [HasDerivedCategory.{w} (modules (constantRing JX A))]
    [HasDerivedCategory.{w} (modules (constantRing JY A))] where
  exactness : CoefficientExactness aX aY
  r : DerivedAdjunction o.pull o.pushR o.adjR
  a : DerivedAdjunction IA.modules o.pushA o.adjA
  exactA : IsIso a.epsilon
  x : DerivedCategory (modules RX) ⥤ DerivedCategory (modules (constantRing JX A))
  y : DerivedCategory (modules RY) ⥤ DerivedCategory (modules (constantRing JY A))
  xFactors : DerivedCategory.Q ⋙ x ≅ onComplex (restriction aX) ⋙ DerivedCategory.Q
  yFactors : DerivedCategory.Q ⋙ y ≅ onComplex (restriction aY) ⋙ DerivedCategory.Q
  flatComparison : ∀ P : CochainComplex (modules RY) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (J := JY) (R := RY) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := JY) (R := RY) (P.X n)) →
      IsIso (r.epsilon.app P)
  tau : y ⋙ a.left ⟶ r.left ⋙ x
  tauFormula : ∀ P : CochainComplex (modules RY) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (J := JY) (R := RY) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := JY) (R := RY) (P.X n)) →
      tau.app (DerivedCategory.Q.obj P) ≫ x.map (r.epsilon.app P) ≫
          xFactors.hom.app ((onComplex o.pull).obj P) =
        a.left.map (yFactors.hom.app P) ≫
          a.epsilon.app ((onComplex (restriction aY)).obj P) ≫
            DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex o.scalarUnit
              (ComplexShape.up ℤ)).app P)
  kappa : r.right ⋙ y ≅ x ⋙ a.right
  kappaFormula : ∀ (I : CochainComplex (modules RX) ℤ), I.IsKInjective →
    ∀ (T : CochainComplex (modules (constantRing JX A)) ℤ), T.IsKInjective →
    ∀ (j : (onComplex (restriction aX)).obj I ⟶ T), ∀ [QuasiIso j],
      yFactors.inv.app ((onComplex o.pushR).obj I) ≫ y.map (r.eta.app I) ≫
          kappa.hom.app (DerivedCategory.Q.obj I) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex o.ordinaryKappa.hom
          (ComplexShape.up ℤ)).app I) ≫
          DerivedCategory.Q.map ((onComplex o.pushA).map j) ≫ a.eta.app T ≫
            a.right.map (inv (DerivedCategory.Q.map j) ≫ xFactors.inv.app I)

variable [IA.modules.Additive]
  {aX : constantRing JX A ⟶ RX} {aY : constantRing JY A ⟶ RY}
  {aI : constantRing JX A ⟶ RI}
  {o : OrdinaryPresentation direct geom IA IR c aX aY aI}
  [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
  [HasDerivedCategory.{w} (modules (constantRing JX A))]
  [HasDerivedCategory.{w} (modules (constantRing JY A))]

end CategoryTheory.RingedCoefficientCounit
