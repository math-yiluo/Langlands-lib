/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Homology.System.SystemOrdinarySingleExtension
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
public import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos
public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtension
public import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
public import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedEvaluation
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Ordinary geometric comparison on strict semilinear systems -/

set_option Elab.async false

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules
open MonoidalCategory
open scoped TensorProduct ChangeOfRings

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  (BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})
  (u : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
  (I : ∀ n : ℕ, AlgebraicInverseImage u.inverse (BY.obj (op n)) (BX.obj (op n)))

/-- The ordinary underlying-set functor at a coefficient level, used only to express
transport of the actual semilinear transition. Source: Zheng, Construction 4.1, p. 21;
Stacks 03D2 (blueprint: lem-pur-system-geometric-ordinary-comparison). -/
abbrev geometricSystemUnderlying (n : ℕ) :=
  toSheaf (derivedChangeRingIndependentCoefficients J (BY.obj (op n))) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- An exact termwise inverse image with its specified underlying transition maps.
The transition equation fixes the functor on systems, rather than merely specifying
unrelated level objects. All exactness fields are conclusions of the existence theorem.
Source: Zheng, Construction 4.1 and the sentence before Lemma 4.10; Stacks 03D2
(blueprint: lem-pur-system-geometric-ordinary-comparison). -/
structure GeometricSystemOrdinaryData where
  functor : StrictRingSystem BY ⥤ StrictRingSystem BX
  [additive : functor.Additive]
  [limits : PreservesFiniteLimits functor]
  [colimits : PreservesFiniteColimits functor]
  [levelAdditive : ∀ n : ℕ, (I n).modules.Additive]
  [levelLimits : ∀ n : ℕ, PreservesFiniteLimits (I n).modules]
  [levelColimits : ∀ n : ℕ, PreservesFiniteColimits (I n).modules]
  evaluation : ∀ n : ℕ,
    functor ⋙ systemEvaluation BX n ≅ systemEvaluation BY n ⋙ (I n).modules
  transition : ∀ (M : StrictRingSystem BY) {m n : ℕ} (h : m ≤ n),
    (geometricSystemUnderlying BX n).map ((evaluation n).hom.app M) ≫
        (I n).moduleUnderlying.hom.app (M.level n) ≫
        u.inverse.map ((geometricSystemUnderlying BY n).map (M.transition h)) ≫
        (I m).moduleUnderlying.inv.app (M.level m) =
      (geometricSystemUnderlying BX n).map ((functor.obj M).transition h) ≫
        (geometricSystemUnderlying BX m).map ((evaluation m).hom.app M)

attribute [instance] GeometricSystemOrdinaryData.additive
  GeometricSystemOrdinaryData.limits GeometricSystemOrdinaryData.colimits

variable {BY BX u I}

/-- The specified level inverse image, retaining the exactness witness in its interface.
Source: Stacks 03D2 (blueprint: lem-pur-system-geometric-ordinary-comparison). -/
def GeometricSystemOrdinaryData.levelInverseImage
    (_F : GeometricSystemOrdinaryData BY BX u I) (n : ℕ) := (I n).modules

/-- Additivity of the level inverse image. Source: Stacks 03D2
(blueprint: lem-pur-system-geometric-ordinary-comparison). -/
instance GeometricSystemOrdinaryData.levelInverseImageAdditive
    (F : GeometricSystemOrdinaryData BY BX u I) (n : ℕ) :
    (F.levelInverseImage n).Additive := F.levelAdditive n

/-- Left exactness of the level inverse image. Source: Stacks 03DA
(blueprint: lem-pur-system-geometric-ordinary-comparison). -/
instance GeometricSystemOrdinaryData.levelInverseImageLimits
    (F : GeometricSystemOrdinaryData BY BX u I) (n : ℕ) :
    PreservesFiniteLimits (F.levelInverseImage n) := F.levelLimits n

/-- Right exactness of the level inverse image. Source: Stacks 03DB
(blueprint: lem-pur-system-geometric-ordinary-comparison). -/
instance GeometricSystemOrdinaryData.levelInverseImageColimits
    (F : GeometricSystemOrdinaryData BY BX u I) (n : ℕ) :
    PreservesFiniteColimits (F.levelInverseImage n) := F.levelColimits n

/-- The canonical localization of the termwise evaluation square.
Source: Zheng, Construction 4.1; Stacks 015F
(blueprint: lem-pur-system-geometric-ordinary-comparison). -/
def GeometricSystemOrdinaryData.derivedEvaluation
    (F : GeometricSystemOrdinaryData BY BX u I) (n : ℕ) :
    F.functor.mapDerivedCategory ⋙ derivedSystemEvaluation BX n ≅
      derivedSystemEvaluation BY n ⋙ (F.levelInverseImage n).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso F.functor (systemEvaluation BX n) ≪≫
    Functor.mapDerivedCategoryNatIso
      (G := systemEvaluation BY n ⋙ F.levelInverseImage n)
      (F.evaluation n : F.functor ⋙ systemEvaluation BX n ≅
        systemEvaluation BY n ⋙ F.levelInverseImage n) ≪≫
    (Functor.mapDerivedCategoryCompIso (systemEvaluation BY n) (F.levelInverseImage n)).symm

/-- Exact termwise inverse image and its ordinary singleton comparison.
Source: Zheng, Construction 4.1, printed p. 21; Stacks 03D2 and 03EL.
(blueprint: lem-pur-system-geometric-ordinary-comparison).

Proof: Conjugate each semilinear transition by the recorded underlying-sheaf
isomorphisms. Test on the universal pairs of sections; the module addition and scalar
operation diagrams imply additivity and semilinearity. The coefficient transition
square supplies compatibility of scalars. Faithfulness of the underlying functors
then proves identities, composition, and naturality. Finite limits and colimits are
preserved levelwise, hence on strict systems by their componentwise universal properties.
Use the balanced coefficient-square construction with identity structural coefficient
maps, and remove identity scalar extensions by their tensor units. Its generator
formula gives the scalar comparison. Take the mate of the exact evaluation square
under the two ordinary singleton adjunctions. Below the selected index the scalar
comparison makes this mate invertible, and above it both objects are zero. Its inverse
is the ordinary comparison. The mate unit identity gives multiplication normalization;
the scalar generator formula gives the specified generalized tensor equation. -/
theorem geometricSystemOrdinaryComparison
    (BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})
    (u : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (I : ∀ n : ℕ, AlgebraicInverseImage u.inverse (BY.obj (op n)) (BX.obj (op n)))
    (htransition : ∀ {m n : ℕ} (h : m ≤ n),
      u.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map
          (BY.map (homOfLE h).op)) ≫ (I m).ringUnderlying.hom =
        (I n).ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map
            (BX.map (homOfLE h).op))
    (SY : SystemScalarAssignment (J := J)) (TY : SystemTensorCoherence SY)
    (SX : SystemScalarAssignment (J := K)) (TX : SystemTensorCoherence SX) :
    ∃ F : GeometricSystemOrdinaryData BY BX u I,
  ∃ (ordinary : ∀ n : ℕ,
      systemSingleFunctor SY TY BY n ⋙ F.functor ≅
        F.levelInverseImage n ⋙ systemSingleFunctor SX TX BX n)
    (tensor : ∀ {j n : ℕ} (h : j ≤ n),
      systemTensor SY BY h ⋙ F.levelInverseImage j ≅
        F.levelInverseImage n ⋙ systemTensor SX BX h),
    (∀ {j n : ℕ} (h : j ≤ n) (P : systemLevel BY n),
    (F.evaluation j).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
        (F.levelInverseImage j).map ((systemSingleBelow SY TY BY n h).hom.app P) ≫
        (tensor h).hom.app P =
      ((ordinary n).hom.app P).app j ≫
        (systemSingleBelow SX TX BX n h).hom.app ((F.levelInverseImage n).obj P)) ∧
    (∀ {j n : ℕ} (h : j ≤ n) (P : systemLevel BY n)
    (Z : Sheaf J (Type w))
    (b : Z ⟶ (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).obj (BY.obj (op j)))
    (x : Z ⟶ (geometricSystemUnderlying BY n).obj P)
    (z : Z ⟶ (geometricSystemUnderlying BY j).obj ((systemTensor SY BY h).obj P)),
    (∀ U t, z.hom.app U t =
      systemModelTmul (SY (BY.map (homOfLE h).op)).model P U
        (b.hom.app U t) (x.hom.app U t)) →
    ∀ (W : Dᵒᵖ) (t : (u.inverse.obj Z).obj.obj W),
      ((tensor h).hom.app P).val.app W
          (((u.inverse.map z) ≫
            (I j).moduleUnderlying.inv.app ((systemTensor SY BY h).obj P)).hom.app W t) =
        systemModelTmul (SX (BX.map (homOfLE h).op)).model
          ((F.levelInverseImage n).obj P) W
          (((u.inverse.map b) ≫ (I j).ringUnderlying.hom).hom.app W t)
          (((u.inverse.map x) ≫ (I n).moduleUnderlying.inv.app P).hom.app W t)) ∧
    (∀ (n j : ℕ) (h : n < j) (P : systemLevel BY n),
    ((ordinary n).hom.app P).app j = 0) ∧
    (∀ (n : ℕ) (P : systemLevel BY n),
    ((ordinary n).hom.app P).app n ≫
        ((systemSingleBelow SX TX BX n (Nat.le_refl n) ≪≫ TX.ordinaryUnit BX n)).hom.app
          ((F.levelInverseImage n).obj P) =
      (F.evaluation n).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
        (F.levelInverseImage n).map
          ((systemSingleBelow SY TY BY n (Nat.le_refl n) ≪≫
            TY.ordinaryUnit BY n).hom.app P)) := by
  sorry

variable (SY : SystemScalarAssignment (J := J)) (TY : SystemTensorCoherence SY)
  (SX : SystemScalarAssignment (J := K)) (TX : SystemTensorCoherence SX)

end SheafOfModules
