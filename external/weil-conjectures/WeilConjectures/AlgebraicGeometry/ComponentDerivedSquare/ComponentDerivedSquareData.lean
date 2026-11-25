/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ZetaWeil.ComponentLiftBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-! # Data for the component square on ordinary unbounded derived categories

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9, and the naturality
used in Corollary 4.4(2) (blueprint: lem-zl-component-derived-pullback-square).

The data structures below spell out the simultaneous witnesses and normalizations of
this one statement. All inverse images are the actual site inverse images. Module
transport uses the existing internal-module encoding and its equivalence with
`ringedSiteModules`; the derived categories and tensors are the ordinary ones.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

/-- The direct image of the relative component site is restriction along the recorded tests.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def componentDirect (X : Scheme.{u}) [IsAffine X]
    (hc : (CondensedRing.componentTests X).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      (Scheme.ProEt.topology X)) :=
  letI := hc
  (CondensedRing.componentTests X).sheafPushforwardContinuous Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
    (Scheme.ProEt.topology X)

/-- Restriction carries the canonical pointwise lax tensor maps.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance componentDirectMonoidal (X : Scheme.{u}) [IsAffine X]
    (hc : (CondensedRing.componentTests X).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      (Scheme.ProEt.topology X)) : (componentDirect X hc).LaxMonoidal := by
  dsimp only [componentDirect]
  infer_instance

/-- The actual component-site adjunction, including its specified unit.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def componentAdjunction (X : Scheme.{u}) [IsAffine X]
    (hc : (CondensedRing.componentTests X).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      (Scheme.ProEt.topology X)) :=
  letI := hc
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (CondensedRing.componentTests X) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
    (Scheme.ProEt.topology X)

/-- The slice projection adjunction; its inverse image is restriction to the slice.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def slicePointAdjunction (P : Profinite.{u}) :=
  (Over.forgetAdjStar P).sheafPushforwardContinuous
    ((coherentTopology Profinite.{u}).over P) (coherentTopology Profinite.{u})
    (E := Ab.{u + 1})

/-- The structural adjunction with absolute profinite tests as its direct image.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def absoluteAdjunction (X : Scheme.{u}) :=
  (pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp profiniteToProEt
        (Scheme.proEtaleBaseChange (toSpecZ X)) Ab.{u + 1}
        (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)
        (Scheme.ProEt.topology X))

/-- Simultaneous site and coefficient witnesses, with canonical adjunctions and
absolute-test normalization. These fields add no hypothesis to the theorem.
Source: HRS construction (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
structure Corner (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X] where
  [continuous : (CondensedRing.componentTests X).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
    (Scheme.ProEt.topology X)
    ]
  inverse : Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      Ab.{u + 1} ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  inverse_eq : inverse = @CondensedRing.componentInverse X _ continuous
  [braided : inverse.Braided]
  [finiteLimits : PreservesFiniteLimits inverse]
  [finiteColimits : PreservesFiniteColimits inverse]
  adjunction : inverse ⊣ componentDirect X continuous
  adjunction_eq : HEq adjunction (componentAdjunction X continuous)
  tensor_canonical : ∀ A B,
    Functor.OplaxMonoidal.δ inverse A B =
      (adjunction.homEquiv _ _).symm
        ((adjunction.unit.app A ⊗ₘ adjunction.unit.app B) ≫
          Functor.LaxMonoidal.μ (componentDirect X continuous)
            (inverse.obj A) (inverse.obj B))
  unit_canonical : Functor.OplaxMonoidal.η inverse =
    (adjunction.homEquiv _ _).symm (Functor.LaxMonoidal.ε (componentDirect X continuous))
  absoluteTests : Over.star (affineComponentSpace X) ⋙ CondensedRing.componentTests X ≅
    profiniteToProEtOf X
  absolute_coordinate : ∀ (S : Profinite.{u})
      (z : ((relativeComponentLift X).obj
        ((Over.star (affineComponentSpace X)).obj S)).left),
    (prod.snd : affineComponentSpace X ⨯ S ⟶ S) (relativeComponentCoordinate X
        ((Over.star (affineComponentSpace X)).obj S) z) =
      profiniteTestProjection X S ((absoluteTests.hom.app S).left z)
  beta : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
      (affineComponentSpace X) ⋙ inverse ≅ upperStarFromPoint X
  [beta_monoidal : NatTrans.IsMonoidal beta.hom]
  beta_mate : ∀ (G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (S : Profinite.{u}),
    (((conjugateIsoEquiv
      ((slicePointAdjunction (affineComponentSpace X)).comp adjunction)
      (absoluteAdjunction X) beta.symm).hom.app G).hom.app (op S)) =
      G.obj.map (absoluteTests.inv.app S).op
  coefficient : inverse.mapMon.obj
      (Mon.mk (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))) ≅
    Mon.mk (condensedRingObj Λ.X X)
  coefficient_eq : coefficient.hom.hom = beta.hom.app Λ.X

attribute [instance] Corner.braided Corner.finiteLimits Corner.finiteColimits
  Corner.beta_monoidal

/-- The actual module inverse image, transporting along the prescribed coefficient iso.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def Corner.modules (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    (s : Corner Λ X) :
    Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace X)) Ab.{u + 1})
      (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X)) ⥤
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X) :=
  s.inverse.mapMod (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X)) ⋙
    Mod.comap s.coefficient.inv.hom

/-- Additivity comes from finite-product preservation of the actual inverse image.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance Corner.modulesAdditive (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    (s : Corner Λ X) : (s.modules Λ X).Additive :=
  letI : PreservesFiniteLimits (s.modules Λ X) := by
    unfold Corner.modules
    infer_instance
  Functor.additive_of_preserves_binary_products _

/-- The actual direct image for a map of component spaces is restriction along base change.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def sliceDirect {P Q : Profinite.{u}} (h : Q ⟶ P) :=
  (Over.pullback h).sheafPushforwardContinuous Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over P) ((coherentTopology Profinite.{u}).over Q)

/-- Slice restriction carries its canonical pointwise lax tensor maps.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance sliceDirectMonoidal {P Q : Profinite.{u}} (h : Q ⟶ P) :
    (sliceDirect h).LaxMonoidal := by
  dsimp only [sliceDirect]
  infer_instance

/-- The inverse image left adjoint to restriction along the profinite base-change functor.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def sliceInverse {P Q : Profinite.{u}} (h : Q ⟶ P) :=
  Functor.sheafPullbackConstruction.sheafPullback (Over.pullback h) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over P) ((coherentTopology Profinite.{u}).over Q)

/-- Its canonical adjunction, used to specify all mate normalizations.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def sliceAdjunction {P Q : Profinite.{u}} (h : Q ⟶ P) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Over.pullback h) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over P) ((coherentTopology Profinite.{u}).over Q)

/-- The coefficient comparison on a profinite slice is fixed by the canonical product map.
Source: HRS construction (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
structure Slice (Λ : Profinite.CondensedRing.{u}) {P Q : Profinite.{u}} (h : Q ⟶ P) where
  inverse : Sheaf ((coherentTopology Profinite.{u}).over P) Ab.{u + 1} ⥤
    Sheaf ((coherentTopology Profinite.{u}).over Q) Ab.{u + 1}
  inverse_eq : inverse = sliceInverse h
  [braided : inverse.Braided]
  [finiteLimits : PreservesFiniteLimits inverse]
  [finiteColimits : PreservesFiniteColimits inverse]
  adjunction : inverse ⊣ sliceDirect h
  adjunction_eq : HEq adjunction (sliceAdjunction h)
  tensor_canonical : ∀ A B,
    Functor.OplaxMonoidal.δ inverse A B =
      (adjunction.homEquiv _ _).symm
        ((adjunction.unit.app A ⊗ₘ adjunction.unit.app B) ≫
          Functor.LaxMonoidal.μ (sliceDirect h) (inverse.obj A) (inverse.obj B))
  unit_canonical : Functor.OplaxMonoidal.η inverse =
    (adjunction.homEquiv _ _).symm (Functor.LaxMonoidal.ε (sliceDirect h))
  beta : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} P ⋙ inverse ≅
    (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} Q
  [beta_monoidal : NatTrans.IsMonoidal beta.hom]
  beta_mate : ∀ (G : Sheaf ((coherentTopology Profinite.{u}).over Q) Ab.{u + 1})
      (S : Profinite.{u}),
    (((conjugateIsoEquiv
      ((slicePointAdjunction P).comp adjunction)
      (slicePointAdjunction Q) beta.symm).hom.app G).hom.app (op S)) =
      G.obj.map ((Over.starPullbackIsoStar h).inv.app S).op
  coefficient : inverse.mapMon.obj (Mon.mk (CondensedRing.profiniteCoefficient Λ.X P)) ≅
    Mon.mk (CondensedRing.profiniteCoefficient Λ.X Q)
  coefficient_eq : coefficient.hom.hom = beta.hom.app Λ.X

attribute [instance] Slice.braided Slice.finiteLimits Slice.finiteColimits Slice.beta_monoidal

/-- The actual slice module inverse image with the canonical coefficient transport.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def Slice.modules (Λ : Profinite.CondensedRing.{u}) {P Q : Profinite.{u}} {h : Q ⟶ P}
    (s : Slice Λ h) :
    Mod (Sheaf ((coherentTopology Profinite.{u}).over P) Ab.{u + 1})
      (CondensedRing.profiniteCoefficient Λ.X P) ⥤
    Mod (Sheaf ((coherentTopology Profinite.{u}).over Q) Ab.{u + 1})
      (CondensedRing.profiniteCoefficient Λ.X Q) :=
  s.inverse.mapMod (CondensedRing.profiniteCoefficient Λ.X P) ⋙
    Mod.comap s.coefficient.inv.hom

/-- Finite limits of the component module pullback are computed on underlying sheaves.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance Corner.modulesFiniteLimits (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u})
    [IsAffine X] (s : Corner Λ X) : PreservesFiniteLimits (s.modules Λ X) := by
  unfold Corner.modules
  infer_instance

/-- Finite colimits of the component module pullback are computed on underlying sheaves.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance Corner.modulesFiniteColimits (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u})
    [IsAffine X] (s : Corner Λ X) : PreservesFiniteColimits (s.modules Λ X) := by
  unfold Corner.modules
  infer_instance

/-- Finite limits of the slice module pullback are computed on underlying sheaves.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance Slice.modulesFiniteLimits (Λ : Profinite.CondensedRing.{u})
    {P Q : Profinite.{u}} {h : Q ⟶ P} (s : Slice Λ h) :
    PreservesFiniteLimits (s.modules Λ) := by
  unfold Slice.modules
  infer_instance

/-- Finite colimits of the slice module pullback are computed on underlying sheaves.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance Slice.modulesFiniteColimits (Λ : Profinite.CondensedRing.{u})
    {P Q : Profinite.{u}} {h : Q ⟶ P} (s : Slice Λ h) :
    PreservesFiniteColimits (s.modules Λ) := by
  unfold Slice.modules
  infer_instance

/-- Additivity of the slice module inverse image.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance Slice.modulesAdditive (Λ : Profinite.CondensedRing.{u})
    {P Q : Profinite.{u}} {h : Q ⟶ P} (s : Slice Λ h) : (s.modules Λ).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Exact module inverse image on the ordinary unbounded derived category.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
@[irreducible]
def Corner.derived (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    (s : Corner Λ X) :
    CondensedRing.Evaluation.D
      ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X)) ⥤
    CondensedRing.Evaluation.D (Scheme.ProEt.topology X) (condensedRingObj Λ.X X) :=
  (s.modules Λ X).mapDerivedCategory

/-- The slice pullback on the ordinary unbounded derived category is termwise localization.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
@[irreducible]
def Slice.derived (Λ : Profinite.CondensedRing.{u})
    {P Q : Profinite.{u}} {h : Q ⟶ P} (s : Slice Λ h) :
    CondensedRing.Evaluation.D ((coherentTopology Profinite.{u}).over P)
      (CondensedRing.profiniteCoefficient Λ.X P) ⥤
    CondensedRing.Evaluation.D ((coherentTopology Profinite.{u}).over Q)
      (CondensedRing.profiniteCoefficient Λ.X Q) :=
  (s.modules Λ).mapDerivedCategory

/-- Identify extension along the scheme coefficient isomorphism with transported scalars.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def schemeUnderlying (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    CondensedRing.upperStar Λ.X f ⋙ Mod.forget (condensedRingObj Λ.X Y) ≅
      Mod.forget (condensedRingObj Λ.X X) ⋙ upperStar Ab.{u + 1} f :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ.X X))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ.X f)))
    (Mod.forget (condensedRingObj Λ.X Y))

/-- The two actual module inverse-image paths for one affine scheme morphism.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
structure Square (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (sX : Corner Λ X) (sY : Corner Λ Y) (sh : Slice Λ (affineComponentMap f)) where
  tests : CondensedRing.componentTests X ⋙ Scheme.proEtaleBaseChange f ≅
    Over.pullback (affineComponentMap f) ⋙ CondensedRing.componentTests Y
  tests_eq : ∀ E : Over (affineComponentSpace X),
    (tests.hom.app E).left = ((component_lift_base_change.choose f).hom.app E).left
  abelian : sX.inverse ⋙ upperStar Ab.{u + 1} f ≅ sh.inverse ⋙ sY.inverse
  abelian_mate : ∀ (G : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (E : Over (affineComponentSpace X)),
    (((conjugateIsoEquiv
      (sh.adjunction.comp sY.adjunction)
      (sX.adjunction.comp (upperStarLowerStarAdjunction Ab.{u + 1} f))
      abelian).hom.app G).hom.app (op E)) = G.obj.map (tests.hom.app E).op
  coefficient :
    (upperStar Ab.{u + 1} f).map sX.coefficient.hom.hom ≫ condensedPullbackHom Λ.X f =
      abelian.hom.app (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X)) ≫
        sY.inverse.map sh.coefficient.hom.hom ≫ sY.coefficient.hom.hom
  ordinary : sX.modules Λ X ⋙ CondensedRing.upperStar Λ.X f ≅
    sh.modules Λ ⋙ sY.modules Λ Y
  ordinary_underlying : ∀ M :
      Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        Ab.{u + 1}) (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X)),
    (ordinary.hom.app M).hom =
      (schemeUnderlying Λ f).hom.app ((sX.modules Λ X).obj M) ≫ abelian.hom.app M.X

/-- The left derived path is the localization of the actual scheme/module inverse images.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
abbrev leftPath (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] (sX : Corner Λ X) (f : Y ⟶ X) :=
  sX.derived Λ X ⋙ (CondensedRing.upperStar Λ.X f).mapDerivedCategory

/-- The right derived path is the localization of the actual slice/module inverse images.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
abbrev rightPath (Λ : Profinite.CondensedRing.{u})
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (sY : Corner Λ Y) (f : Y ⟶ X) (sh : Slice Λ (affineComponentMap f)) :=
  sh.derived Λ ⋙ sY.derived Λ Y

/-- The derived square is the specified termwise module comparison, localized, with
both canonical derived composition comparisons inserted.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
@[irreducible]
def Square.theta (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] {f : Y ⟶ X}
    {sX : Corner Λ X} {sY : Corner Λ Y} {sh : Slice Λ (affineComponentMap f)}
    (sq : Square Λ f sX sY sh) : leftPath Λ sX f ≅ rightPath Λ sY f sh := by
  unfold leftPath rightPath Corner.derived Slice.derived
  exact
    letI : (CondensedRing.upperStar Λ.X f).Additive :=
      CondensedRing.upperStar_additive Λ.X f
    letI : PreservesFiniteLimits (CondensedRing.upperStar Λ.X f) :=
      CondensedRing.preservesFiniteLimits_upperStar Λ.X f
    letI : PreservesFiniteColimits (CondensedRing.upperStar Λ.X f) :=
      CondensedRing.preservesFiniteColimits_upperStar Λ.X f
    letI := comp_preservesFiniteLimits (sX.modules Λ X) (CondensedRing.upperStar Λ.X f)
    letI := comp_preservesFiniteColimits (sX.modules Λ X) (CondensedRing.upperStar Λ.X f)
    letI := comp_preservesFiniteLimits (sh.modules Λ) (sY.modules Λ Y)
    letI := comp_preservesFiniteColimits (sh.modules Λ) (sY.modules Λ Y)
    letI : (sX.modules Λ X ⋙ CondensedRing.upperStar Λ.X f).Additive :=
      inferInstance
    letI : (sh.modules Λ ⋙ sY.modules Λ Y).Additive := inferInstance
    Functor.mapDerivedCategoryCompIso (sX.modules Λ X)
        (CondensedRing.upperStar Λ.X f) ≪≫
      Functor.mapDerivedCategoryNatIso sq.ordinary ≪≫
        (Functor.mapDerivedCategoryCompIso (sh.modules Λ) (sY.modules Λ Y)).symm

/-- The ordinary component module tensor is the existing transported relative tensor.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance Corner.modulesMonoidal (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) [IsAffine X] (s : Corner Λ X) : (s.modules Λ X).Monoidal := by
  unfold Corner.modules
  infer_instance

/-- The ordinary slice module tensor is the existing transported relative tensor.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance Slice.modulesMonoidal (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {P Q : Profinite.{u}} {h : Q ⟶ P} (s : Slice Λ h) : (s.modules Λ).Monoidal := by
  unfold Slice.modules
  infer_instance

section Tensor
universe v w
variable {C D : Type w} [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v} D]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v} D]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [BraidedCategory C] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Monoidal]

/-- The ordinary derived monoidal structure is normalized by termwise tensor and Q.
The braidings are the existing Koszul braidings, rather than unspecified structures.
Source: HRS Section 3 and (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
structure TensorLift where
  [colimits : PreservesColimitsOfSize.{0, 0} F]
  [monoidal : F.mapDerivedCategory.Monoidal]
  localization : NatTrans.IsMonoidal F.mapDerivedCategoryFactors.hom
  triangulated : F.mapDerivedCategory.IsTriangulated
  symmetric : ∀ K L : DerivedCategory C,
    Functor.LaxMonoidal.μ F.mapDerivedCategory K L ≫
        F.mapDerivedCategory.map ((DerivedCategory.braidedCategory' C).braiding K L).hom =
      ((DerivedCategory.braidedCategory' D).braiding
        (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj L)).hom ≫
          Functor.LaxMonoidal.μ F.mapDerivedCategory L K

end Tensor

/-- Identity on the actual slice pullback, normalized by the projection of the test object.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
structure SliceIdentity (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    (s : Slice Λ (affineComponentMap (𝟙 X))) where
  tests : Over.pullback (affineComponentMap (𝟙 X)) ≅ 𝟭 (Over (affineComponentSpace X))
  tests_projection : ∀ E, (tests.hom.app E).left =
    pullback.fst E.hom (affineComponentMap (𝟙 X))
  abelian : s.inverse ≅ 𝟭 _
  abelian_mate : ∀ (G : Sheaf
      ((coherentTopology Profinite.{u}).over (affineComponentSpace X)) Ab.{u + 1}) E,
    (((conjugateIsoEquiv s.adjunction (Adjunction.id) abelian.symm).hom.app G).hom.app
      (op E)) = G.obj.map (tests.inv.app E).op
  ordinary : s.modules Λ ≅ 𝟭 _
  ordinary_underlying : ∀ M, (ordinary.hom.app M).hom = abelian.hom.app M.X

/-- Composition of slice inverse images, with both test-object projections prescribed.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
structure SliceComposition (Λ : Profinite.CondensedRing.{u})
    {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (g : Z ⟶ Y)
    (sf : Slice Λ (affineComponentMap f)) (sg : Slice Λ (affineComponentMap g))
    (sfg : Slice Λ (affineComponentMap (g ≫ f))) where
  tests : Over.pullback (affineComponentMap (g ≫ f)) ≅
    Over.pullback (affineComponentMap f) ⋙ Over.pullback (affineComponentMap g)
  tests_fst : ∀ E,
    (tests.hom.app E).left ≫
        pullback.fst ((Over.pullback (affineComponentMap f)).obj E).hom
          (affineComponentMap g) ≫ pullback.fst E.hom (affineComponentMap f) =
      pullback.fst E.hom (affineComponentMap (g ≫ f))
  tests_snd : ∀ E,
    (tests.hom.app E).left ≫
        pullback.snd ((Over.pullback (affineComponentMap f)).obj E).hom
          (affineComponentMap g) = pullback.snd E.hom (affineComponentMap (g ≫ f))
  abelian : sfg.inverse ≅ sf.inverse ⋙ sg.inverse
  abelian_mate : ∀ (G : Sheaf
      ((coherentTopology Profinite.{u}).over (affineComponentSpace Z)) Ab.{u + 1}) E,
    (((conjugateIsoEquiv sfg.adjunction (sf.adjunction.comp sg.adjunction)
      abelian.symm).hom.app G).hom.app (op E)) = G.obj.map (tests.inv.app E).op
  ordinary : sfg.modules Λ ≅ sf.modules Λ ⋙ sg.modules Λ
  ordinary_underlying : ∀ M, (ordinary.hom.app M).hom = abelian.hom.app M.X

/-- Derived identity of a slice pullback, obtained by the existing localization operation.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
@[irreducible]
def SliceIdentity.derived (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    {s : Slice Λ (affineComponentMap (𝟙 X))} (i : SliceIdentity Λ X s) :
    s.derived Λ ≅ 𝟭 _ := by
  unfold Slice.derived
  exact Functor.mapDerivedCategoryNatIso i.ordinary ≪≫ Functor.mapDerivedCategoryIdIso _

/-- Derived slice composition, with the existing canonical localization comparisons.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
@[irreducible]
def SliceComposition.derived (Λ : Profinite.CondensedRing.{u})
    {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    {f : Y ⟶ X} {g : Z ⟶ Y}
    {sf : Slice Λ (affineComponentMap f)} {sg : Slice Λ (affineComponentMap g)}
    {sfg : Slice Λ (affineComponentMap (g ≫ f))}
    (c : SliceComposition Λ f g sf sg sfg) :
    sfg.derived Λ ≅ sf.derived Λ ⋙ sg.derived Λ := by
  unfold Slice.derived
  exact
    letI := comp_preservesFiniteLimits (sf.modules Λ) (sg.modules Λ)
    letI := comp_preservesFiniteColimits (sf.modules Λ) (sg.modules Λ)
    Functor.mapDerivedCategoryNatIso c.ordinary ≪≫
      (Functor.mapDerivedCategoryCompIso (sf.modules Λ) (sg.modules Λ)).symm

/-- Derived scheme identity, with the published ordinary identity and localization maps.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
@[irreducible]
def schemeIdentity (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :
    (CondensedRing.upperStar Λ.X (𝟙 X)).mapDerivedCategory ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ.X X) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Derived scheme composition, with the published ordinary adjunction comparison.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
@[irreducible]
def schemeComposition (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    (CondensedRing.upperStar Λ.X (g ≫ f)).mapDerivedCategory ≅
      (CondensedRing.upperStar Λ.X f).mapDerivedCategory ⋙
        (CondensedRing.upperStar Λ.X g).mapDerivedCategory :=
  letI := comp_preservesFiniteLimits (CondensedRing.upperStar Λ.X f)
    (CondensedRing.upperStar Λ.X g)
  letI := comp_preservesFiniteColimits (CondensedRing.upperStar Λ.X f)
    (CondensedRing.upperStar Λ.X g)
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ.X g f) ≪≫
    (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ.X f)
      (CondensedRing.upperStar Λ.X g)).symm

section TensorSquare
universe v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄

/-- Monoidality of a square with four explicitly supplied tensor structures.
Keeping the structures as parameters avoids recomputing their derived constructions.
Source: the tensor and unit equations of HRS (4.1)
(blueprint: def-zl-component-derived-square-data). -/
def tensorSquareMonoidal
    {A : Type w₁} [Category.{v₁} A] [MonoidalCategory A]
    {B : Type w₂} [Category.{v₂} B] [MonoidalCategory B]
    {C : Type w₃} [Category.{v₃} C] [MonoidalCategory C]
    {D : Type w₄} [Category.{v₄} D] [MonoidalCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    (tF : F.Monoidal) (tG : G.Monoidal) (tH : H.Monoidal) (tI : I.Monoidal)
    (e : F ⋙ G ≅ H ⋙ I) : Prop :=
  letI := tF
  letI := tG
  letI := tH
  letI := tI
  NatTrans.IsMonoidal e.hom

end TensorSquare

/-- Monoidality of the specified comparison, with canonical termwise-localized structures.
This includes the coefficient-unit equation and both tensor comparisons.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def Square.monoidal (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] {f : Y ⟶ X}
    {sX : Corner Λ X} {sY : Corner Λ Y} {sh : Slice Λ (affineComponentMap f)}
    (sq : Square Λ f sX sY sh)
    (tX : TensorLift (sX.modules Λ X)) (tY : TensorLift (sY.modules Λ Y))
    (tf : TensorLift (CondensedRing.upperStar Λ.X f)) (th : TensorLift (sh.modules Λ)) : Prop :=
  tensorSquareMonoidal (sX.derived Λ X)
    (CondensedRing.upperStar Λ.X f).mapDerivedCategory
    (sh.derived Λ) (sY.derived Λ Y)
    (by unfold Corner.derived; exact tX.monoidal) tf.monoidal
    (by unfold Slice.derived; exact th.monoidal)
    (by unfold Corner.derived; exact tY.monoidal) (sq.theta Λ)

section SquareCoherence
universe v₁ v₂ v₃ v₄ v₅ v₆ w₁ w₂ w₃ w₄ w₅ w₆

/-- The identity equation of an isomorphism square, kept independent of its construction.
Source: HRS (4.1) (blueprint: def-zl-component-derived-square-data). -/
def squareIdentity
    {A : Type w₁} [Category.{v₁} A] {B : Type w₂} [Category.{v₂} B]
    (F : A ⥤ B) (G : B ⥤ B) (H : A ⥤ A)
    (e : F ⋙ G ≅ H ⋙ F) (i : H ≅ 𝟭 A) (j : G ≅ 𝟭 B) : Prop :=
  ∀ M, e.hom.app M ≫ F.map (i.hom.app M) = j.hom.app (F.obj M)

/-- The pasting equation of two isomorphism squares, independent of the edge constructions.
Source: HRS (4.1) (blueprint: def-zl-component-derived-square-data). -/
def squareComposition
    {A : Type w₁} [Category.{v₁} A] {B : Type w₂} [Category.{v₂} B]
    {C : Type w₃} [Category.{v₃} C] {D : Type w₄} [Category.{v₄} D]
    {E : Type w₅} [Category.{v₅} E] {T : Type w₆} [Category.{v₆} T]
    (a : A ⥤ B) (b : C ⥤ D) (c : E ⥤ T)
    (f : B ⥤ D) (g : D ⥤ T) (fg : B ⥤ T)
    (h : A ⥤ C) (k : C ⥤ E) (hk : A ⥤ E)
    (ef : a ⋙ f ≅ h ⋙ b) (eg : b ⋙ g ≅ k ⋙ c) (efg : a ⋙ fg ≅ hk ⋙ c)
    (i : fg ≅ f ⋙ g) (j : hk ≅ h ⋙ k) : Prop :=
  ∀ M, i.hom.app (a.obj M) ≫ g.map (ef.hom.app M) ≫ eg.hom.app (h.obj M) =
    efg.hom.app M ≫ c.map (j.hom.app M)

end SquareCoherence

/-- A single coherent family of the square, its exact symmetric tensor structures and
its termwise descent. Identity/composition maps are normalized by test-object projections.
Source: HRS (4.1), Corollary 4.4(2)
(blueprint: lem-zl-component-derived-pullback-square). -/
structure System (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] where
  corner : ∀ (X : Scheme.{u}) [IsAffine X], Corner Λ X
  slice : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    Slice Λ (affineComponentMap f)
  square : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    Square Λ f (corner X) (corner Y) (slice f)
  cornerTensor : ∀ (X : Scheme.{u}) [IsAffine X], TensorLift ((corner X).modules Λ X)
  sliceTensor : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    TensorLift ((slice f).modules Λ)
  schemeTensor : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    TensorLift (CondensedRing.upperStar Λ.X f)
  monoidal : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    (square f).monoidal Λ (cornerTensor X) (cornerTensor Y) (schemeTensor f) (sliceTensor f)
  sliceIdentity : ∀ (X : Scheme.{u}) [IsAffine X], SliceIdentity Λ X (slice (𝟙 X))
  sliceComposition : ∀ {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (g : Z ⟶ Y),
    SliceComposition Λ f g (slice f) (slice g) (slice (g ≫ f))
  identity : ∀ (X : Scheme.{u}) [IsAffine X],
    squareIdentity ((corner X).derived Λ X)
      (CondensedRing.upperStar Λ.X (𝟙 X)).mapDerivedCategory ((slice (𝟙 X)).derived Λ)
      ((square (𝟙 X)).theta Λ) ((sliceIdentity X).derived Λ X) (schemeIdentity Λ X)
  composition : ∀ (X Y Z : Scheme.{u}) [IsAffine X] [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y),
    squareComposition ((corner X).derived Λ X) ((corner Y).derived Λ Y)
      ((corner Z).derived Λ Z) (CondensedRing.upperStar Λ.X f).mapDerivedCategory
      (CondensedRing.upperStar Λ.X g).mapDerivedCategory
      (CondensedRing.upperStar Λ.X (g ≫ f)).mapDerivedCategory
      ((slice f).derived Λ) ((slice g).derived Λ) ((slice (g ≫ f)).derived Λ)
      ((square f).theta Λ) ((square g).theta Λ) ((square (g ≫ f)).theta Λ)
      (schemeComposition Λ f g) ((sliceComposition f g).derived Λ)
  cornerDuals : ∀ (X : Scheme.{u}) [IsAffine X]
      (K : CondensedRing.Evaluation.D
        ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    IsDualizable K → IsDualizable (((corner X).derived Λ X).obj K)
  sliceDuals : ∀ (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
      (K : CondensedRing.Evaluation.D
        ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    IsDualizable K → IsDualizable (((slice f).derived Λ).obj K)
  schemeDuals : ∀ (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
      (K : CondensedRing.Evaluation.D (Scheme.ProEt.topology X) (condensedRingObj Λ.X X)),
    IsDualizable K → IsDualizable ((CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj K)

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
