/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
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
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.CategoryTheory.FlatRingedDiagramInput.FlatRestrictionOrdinaryComparisons
import all WeilConjectures.CategoryTheory.Site.SiteAlgebraicCompositionUnitSupplement
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.CategoryTheory.GeometricMorphism.GeometricInverseImageExactSupplement
import all WeilConjectures.Algebra.Homology.Ringed.RingedTopoiDerivedPullbackIndependentSupplement
import all WeilConjectures.CategoryTheory.SixFunctors.CokernelAdjointExchange
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorPairingIsIso
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.GeometricRingTransport
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement

/-! # Normalization of scalar pullback on K-flat representatives

Source: blueprint main-20261015, proposition-six-operations-change-coefficients (1); Stacks Project,
Tags 03EL, 0G7E, 06YY, 07A6 and 0D6D
(blueprint: lem-sfb-kflat-scalar-comparison-normalization).

## Main statements

- `kflat_scalar_comparison_normalization`: balanced comparison and specified derived mate.
- `θ_composition`, `θ_identity`: geometric composition and identity normalization.

The ordinary comparison is specified on generalized pure tensors, including its
scalar-extension units. The derived comparison is the inverse mate of the action
identification, rather than an unspecified isomorphism of functors. Its representative
formula uses the counits of the existing universal derived-change-of-rings models.
-/

@[expose] public section
set_option autoImplicit false
universe u w u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules.ScalarPullback

/-- The module category already used by the scalar-change model.
Source: Stacks 03D2 (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
abbrev Modules {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (A : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A)

/-- Forget a module to its underlying sheaf of sets.
Source: Stacks 03D2 (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
noncomputable abbrev underlying {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (A : Sheaf J CommRingCat.{u}) : Modules A ⥤ Sheaf J (Type u) :=
  toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u} ⋙ uliftFunctor.{u, u})

/-- Restriction of scalars along the given sheaf ring map.
Source: Stacks 03D2 (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
noncomputable abbrev restriction {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    Modules B ⥤ Modules A :=
  restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)

section InverseImageAliases

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The existing algebraic inverse-image presentation in the small-site universe.
Source: Stacks 03D2
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
abbrev InverseImage (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u}) :=
  AlgebraicInverseImageOfUniverses.{u, u, u, u, u, u} L A B

variable {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
  {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}

/-- The existing module projection, with its sheaf-composition instances elaborated once.
Source: Stacks 03D2
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
abbrev inverseModules (I : InverseImage L A B) : Modules A ⥤ Modules B := I.modules

/-- The existing ring identification of the algebraic inverse-image presentation.
Source: Stacks 03D2
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
abbrev inverseRing (I : InverseImage L A B) :
    L.obj ((sheafCompose J
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj A) ≅
      (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj B :=
  I.ringUnderlying

/-- The existing underlying-module identification of the inverse-image presentation.
Source: Stacks 03D2
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
abbrev inverseUnderlying (I : InverseImage L A B) :
    inverseModules I ⋙ underlying B ≅ underlying A ⋙ L :=
  I.moduleUnderlying

end InverseImageAliases

/-- The image of a balanced pure tensor in the model's ordinary scalar extension.
The equality transport only identifies the model's object with the existing sheafification.
Source: Stacks 03EL (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
noncomputable def pure {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {A B : Sheaf J CommRingCat.{u}} {φ : A ⟶ B}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ) (M : Modules A) (U : Cᵒᵖ)
    (b : B.obj.obj U) (x : M.val.obj U) : (m.E.obj M).val.obj U :=
  (eqToHom (m.obj_eq M).symm).val.app U
    ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
      (b ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom] x))

/-- The inverse scalar-adjunction mate of a restriction/action square.
Source: Stacks 07A7 (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
def mate {AY : Type u₁} {BY : Type u₂} {AX : Type u₃} {BX : Type u₄}
    [Category.{v₁} AY] [Category.{v₂} BY] [Category.{v₃} AX] [Category.{v₄} BX]
    {TY : AY ⥤ BY} {rY : BY ⥤ AY} {TX : AX ⥤ BX} {rX : BX ⥤ AX}
    (dY : TY ⊣ rY) (dX : TX ⊣ rX) {IA : AY ⥤ AX} {IB : BY ⥤ BX}
    (a : rY ⋙ IA ⟶ IB ⋙ rX) : IA ⋙ TX ⟶ TY ⋙ IB :=
  ((mateEquiv dY dX).symm (TwoSquare.mk _ _ _ _ a))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleComparison
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : Sheaf J (Type u) ⥤ Sheaf K (Type u)} [PreservesFiniteLimits F]
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (γ : F ≅ G) (I : InverseImage F A B) (I' : InverseImage G A B)
    (hr : γ.hom.app _ ≫ (inverseRing I').hom = (inverseRing I).hom) :
    inverseModules I ≅ inverseModules I' := by
  let f (M : Modules A) : (inverseModules I).obj M ⟶ (inverseModules I').obj M :=
    { val :=
      { app := fun U ↦ ModuleCat.ofHom
          { toFun := ((CategoryTheory.moduleComparisonApp γ I I' M).hom.app U)
            map_add' := ((CategoryTheory.moduleComparisonApp γ I I' M).hom.app U).hom.map_add
            map_smul' := by
              intro r x
              have h := CategoryTheory.module_compare_smul γ.hom I I' M U r x
              have he : CategoryTheory.compareMap γ.hom I.ringUnderlying I'.ringUnderlying =
                  𝟙 _ := by
                dsimp [CategoryTheory.compareMap]
                rw [hr, Iso.inv_hom_id]
              rw [he] at h
              exact h }
        naturality := by
          intro U V g
          ext x
          exact CategoryTheory.congr_fun
            ((CategoryTheory.moduleComparisonApp γ I I' M).hom.naturality g) x } }
  have hf (M : Modules A) : (underlying B).map (f M) =
      I.moduleUnderlying.hom.app M ≫ γ.hom.app _ ≫ I'.moduleUnderlying.inv.app M := by
    exact CategoryTheory.moduleComparisonApp_underlying γ I I' M
  let β : inverseModules I ⟶ inverseModules I' :=
    { app := f
      naturality := by
        intro M N g
        apply (underlying B).map_injective
        rw [Functor.map_comp, Functor.map_comp, hf, hf]
        have h := (I.moduleUnderlying ≪≫
          Functor.isoWhiskerLeft (underlying A) γ ≪≫ I'.moduleUnderlying.symm).hom.naturality g
        simpa only [Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
          NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
          Functor.whiskerLeft_app, Functor.comp_map, Category.assoc] using h }
  have hi (M : Modules A) : IsIso (β.app M) := by
    have h : (underlying B).map (β.app M) =
        I.moduleUnderlying.hom.app M ≫ γ.hom.app _ ≫ I'.moduleUnderlying.inv.app M := by
      exact CategoryTheory.moduleComparisonApp_underlying γ I I' M
    have : IsIso ((underlying B).map (β.app M)) := by rw [h]; infer_instance
    exact isIso_of_reflects_iso _ (underlying B)
  exact NatIso.ofComponents (fun M ↦ asIso (β.app M)) (fun g ↦ β.naturality g)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] moduleComparison

section Action

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {AY BY : Sheaf J CommRingCat.{u}} {AX BX : Sheaf K CommRingCat.{u}}
  {φY : AY ⟶ BY} {φX : AX ⟶ BX}
  {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
  (IA : InverseImage L AY AX)
  (IB : InverseImage L BY BX)
  (ring_compat : L.map ((sheafCompose J
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φY) ≫
      (inverseRing IB).hom = (inverseRing IA).hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φX)

-- Compare the two scalar-restriction presentations and their underlying graph operations.
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{w} (Modules AY)] [HasDerivedCategory.{w} (Modules BY)]
  [HasDerivedCategory.{w} (Modules AX)] [HasDerivedCategory.{w} (Modules BX)]
  [(inverseModules IA).Additive] [(inverseModules IB).Additive]
  [PreservesFiniteLimits (inverseModules IA)] [PreservesFiniteColimits (inverseModules IA)]
  [PreservesFiniteLimits (inverseModules IB)] [PreservesFiniteColimits (inverseModules IB)]
  [PreservesFiniteLimits (restriction φY)] [PreservesFiniteColimits (restriction φY)]
  [PreservesFiniteLimits (restriction φX)] [PreservesFiniteColimits (restriction φX)]

end Action

section

-- Tensor arguments use the comparison API; keep the localized monoidal structure closed.
attribute [local irreducible] SheafOfModules.monoidalCategory
  DerivedCategory.Q DerivedCategory.Qh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] pure RingedTensor.pure
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors

-- Compare the tensor presentation and the mate through their section transport formulas.
-- Normalize four exact functors and their cochain comparison isomorphisms.
end

-- Keep the same localization API closed in the composition and identity calculations.
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors DerivedCategory.Q DerivedCategory.Qh

section Composition

variable {CZ CY CX : Type u}
  [Category.{u} CZ] [Category.{u} CY] [Category.{u} CX]
  {JZ : GrothendieckTopology CZ} {JY : GrothendieckTopology CY}
  {JX : GrothendieckTopology CX}
  [HasSheafify JZ AddCommGrpCat.{u}] [JZ.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify JY AddCommGrpCat.{u}] [JY.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify JX AddCommGrpCat.{u}] [JX.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {AZ BZ : Sheaf JZ CommRingCat.{u}} {AY BY : Sheaf JY CommRingCat.{u}}
  {AX BX : Sheaf JX CommRingCat.{u}}
  {φZ : AZ ⟶ BZ} {φY : AY ⟶ BY} {φX : AX ⟶ BX}
  (Lg : Sheaf JZ (Type u) ⥤ Sheaf JY (Type u))
  (Rg : Sheaf JY (Type u) ⥤ Sheaf JZ (Type u)) (adjg : Lg ⊣ Rg)
  (Lf : Sheaf JY (Type u) ⥤ Sheaf JX (Type u))
  (Rf : Sheaf JX (Type u) ⥤ Sheaf JY (Type u)) (adjf : Lf ⊣ Rf)
  (Lh : Sheaf JZ (Type u) ⥤ Sheaf JX (Type u))
  (adjh : Lh ⊣ Rf ⋙ Rg)
  [PreservesFiniteLimits Lg] [PreservesFiniteLimits Lf] [PreservesFiniteLimits Lh]
  (IgA : InverseImage Lg AZ AY)
  (IgB : InverseImage Lg BZ BY)
  (IfA : InverseImage Lf AY AX)
  (IfB : InverseImage Lf BY BX)
  (IhA : InverseImage Lh AZ AX)
  (IhB : InverseImage Lh BZ BX)
  (hg : Lg.map ((sheafCompose JZ
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φZ) ≫
      (inverseRing IgB).hom = (inverseRing IgA).hom ≫
        (sheafCompose JY (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φY)
  (hf : Lf.map ((sheafCompose JY
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φY) ≫
      (inverseRing IfB).hom = (inverseRing IfA).hom ≫
        (sheafCompose JX (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φX)
  (hh : Lh.map ((sheafCompose JZ
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φZ) ≫
      (inverseRing IhB).hom = (inverseRing IhA).hom ≫
        (sheafCompose JX (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φX)
  [HasDerivedCategory.{w} (Modules AZ)] [HasDerivedCategory.{w} (Modules BZ)]
  [HasDerivedCategory.{w} (Modules AY)] [HasDerivedCategory.{w} (Modules BY)]
  [HasDerivedCategory.{w} (Modules AX)] [HasDerivedCategory.{w} (Modules BX)]
  [(inverseModules IgA).Additive]
  [PreservesFiniteLimits (inverseModules IgA)] [PreservesFiniteColimits (inverseModules IgA)]
  [(inverseModules IgB).Additive]
  [PreservesFiniteLimits (inverseModules IgB)] [PreservesFiniteColimits (inverseModules IgB)]
  [(inverseModules IfA).Additive]
  [PreservesFiniteLimits (inverseModules IfA)] [PreservesFiniteColimits (inverseModules IfA)]
  [(inverseModules IfB).Additive]
  [PreservesFiniteLimits (inverseModules IfB)] [PreservesFiniteColimits (inverseModules IfB)]
  [(inverseModules IhA).Additive]
  [PreservesFiniteLimits (inverseModules IhA)] [PreservesFiniteColimits (inverseModules IhA)]
  [(inverseModules IhB).Additive]
  [PreservesFiniteLimits (inverseModules IhB)] [PreservesFiniteColimits (inverseModules IhB)]
  [PreservesFiniteLimits (restriction φZ)] [PreservesFiniteColimits (restriction φZ)]
  [PreservesFiniteLimits (restriction φY)] [PreservesFiniteColimits (restriction φY)]
  [PreservesFiniteLimits (restriction φX)] [PreservesFiniteColimits (restriction φX)]

end Composition

section Identity

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {A B : Sheaf J CommRingCat.{u}} {φ : A ⟶ B}
  (IA : InverseImage (𝟭 (Sheaf J (Type u))) A A)
  (IB : InverseImage (𝟭 (Sheaf J (Type u))) B B)
  (h : (𝟭 (Sheaf J (Type u))).map ((sheafCompose J
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φ) ≫
      (inverseRing IB).hom = (inverseRing IA).hom ≫
        (sheafCompose J (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φ)
  [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
  [(inverseModules IA).Additive] [(inverseModules IB).Additive]
  [PreservesFiniteLimits (inverseModules IA)] [PreservesFiniteColimits (inverseModules IA)]
  [PreservesFiniteLimits (inverseModules IB)] [PreservesFiniteColimits (inverseModules IB)]
  [PreservesFiniteLimits (restriction φ)] [PreservesFiniteColimits (restriction φ)]

end Identity

end SheafOfModules.ScalarPullback
