/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement

import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian

/-! # Ringed-topos derived pullback with independent site universes

Source: Stacks Project, sites-cohomology.tex, Tag 06YY (lemma-derived-base-change).
(blueprint: lem-weil-pbc-ringed-topoi-derived-pullback).

This generalizes the existing interface to sites small relative to the coefficient
universe, keeping their object and morphism universes independent. The original
specialized declaration is retained by public import.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe uC vC uD vD r w
open CategoryTheory CategoryTheory.Limits
open WeilConjectures.SemilinearSections (Mod)
namespace SheafOfModules

private noncomputable abbrev moduleUnderlying
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r}) :=
  toSheaf ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})

private theorem moduleUnderlying_finiteLimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r}) : PreservesFiniteLimits (moduleUnderlying R) := by
  let V := sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})
  have : PreservesFiniteLimits (V ⋙ sheafToPresheaf J (Type r)) :=
    show PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{r} ⋙
      (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{r})) from
        comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits V :=
    preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type r))
  exact comp_preservesFiniteLimits _ _

private theorem moduleUnderlying_epi
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r}) : (moduleUnderlying R).PreservesEpimorphisms := by
  let V := sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})
  have : V.PreservesEpimorphisms := ⟨fun {M N} f hf ↦ by
    have : Sheaf.IsLocallySurjective f :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{r} f).2 hf
    exact inferInstance⟩
  exact inferInstanceAs ((toSheaf _ ⋙ V).PreservesEpimorphisms)

private theorem algebraicInverseImage_finiteLimits
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{r}} {RI : Sheaf JD CommRingCat.{r}}
    (L : Sheaf JC (Type r) ⥤ Sheaf JD (Type r)) [PreservesFiniteLimits L]
    (I : AlgebraicInverseImage L R RI) : PreservesFiniteLimits I.modules := by
  have := moduleUnderlying_finiteLimits R
  have := moduleUnderlying_finiteLimits RI
  have : PreservesFiniteLimits (moduleUnderlying R ⋙ L) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (I.modules ⋙ moduleUnderlying RI) :=
    preservesFiniteLimits_of_natIso I.moduleUnderlying.symm
  exact preservesFiniteLimits_of_reflects_of_preserves I.modules (moduleUnderlying RI)

private theorem algebraicInverseImage_epi
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{r}} {RI : Sheaf JD CommRingCat.{r}}
    (L : Sheaf JC (Type r) ⥤ Sheaf JD (Type r))
    (V : Sheaf JD (Type r) ⥤ Sheaf JC (Type r)) (adj : L ⊣ V)
    (I : AlgebraicInverseImage L R RI) : I.modules.PreservesEpimorphisms := by
  have := moduleUnderlying_epi R
  have := adj.leftAdjoint_preservesColimits
  constructor
  intro M N f hf
  apply (moduleUnderlying RI).epi_of_epi_map
  have : Epi ((moduleUnderlying R ⋙ L).map f) := inferInstance
  have hn := I.moduleUnderlying.hom.naturality f
  have : Epi ((I.modules ⋙ moduleUnderlying RI).map f ≫
      I.moduleUnderlying.hom.app N) := by
    rw [hn]
    infer_instance
  exact (epi_comp_iff_of_isIso _ (I.moduleUnderlying.hom.app N)).1 this

private noncomputable def scalarExtensionPresheaf
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{r}} (c : R ⟶ S) :
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
      PresheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj where
  obj M := changeOfRingsPresheaf.{vC, uC, r} c M
  map {M N} f :=
    { app := fun U ↦ (ModuleCat.extendScalars (c.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturality.{vC, uC, r} c M f }
  map_id M := by
    ext U : 1
    simp
    rfl
  map_comp f g := by
    ext U : 1
    exact (ModuleCat.extendScalars (c.hom.app U).hom).map_comp _ _

private theorem scalarExtensionPresheaf_additive
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{r}} (c : R ⟶ S) :
    (scalarExtensionPresheaf c).Additive where
  map_add {M N} f g := by
    ext U : 1
    have : (ModuleCat.extendScalars (c.hom.app U).hom).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (c.hom.app U).hom).left_adjoint_additive
    simpa only [scalarExtensionPresheaf, add_val, PresheafOfModules.add_app] using
      (ModuleCat.extendScalars (c.hom.app U).hom).map_add
        (f := f.val.app U) (g := g.val.app U)

private noncomputable def scalarExtension
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{r}} (c : R ⟶ S) :
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S) :=
  scalarExtensionPresheaf c ⋙ PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)

private theorem scalarExtension_additive
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{r}} (c : R ⟶ S) :
    (scalarExtension c).Additive := by
  have hsheaf : (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 _)).left_adjoint_additive
  have := scalarExtensionPresheaf_additive c
  dsimp only [scalarExtension]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarExtensionPresheafIdIso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r})
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    M.val ≅ (scalarExtensionPresheaf (𝟙 R)).obj M := by
  refine PresheafOfModules.isoMk
    (fun U ↦ ((ModuleCat.extendScalarsId (R.obj.obj U)).app (M.val.obj U)).symm) ?_
  intro U V i
  ext m
  change (ModuleCat.extendScalarsId (R.obj.obj V)).inv.app (M.val.obj V)
      (M.val.map i m) =
    changeOfRingsMap (𝟙 R) M i
      ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (M.val.obj U) m)
  rw [ModuleCat.extendScalarsId_inv_app_apply, ModuleCat.extendScalarsId_inv_app_apply]
  simpa [changeOfRingsMap] using
    (Classical.choose_spec (exists_changeOfRingsMap (𝟙 R) M i)
      (1 : R.obj.obj U) m).symm

private noncomputable def scalarExtensionIdIsoApp
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r})
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    (scalarExtension (𝟙 R)).obj M ≅ M :=
  (PresheafOfModules.sheafification (𝟙 _)).mapIso
      (scalarExtensionPresheafIdIso R M).symm ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.app M)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarExtensionIdIso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r}) : scalarExtension (𝟙 R) ≅ 𝟭 _ := by
  refine NatIso.ofComponents (scalarExtensionIdIsoApp R) ?_
  intro M N a
  let F := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)
  let ψ := (scalarExtensionPresheaf (𝟙 R)).map a
  have hp : (scalarExtensionPresheafIdIso R M).hom ≫ ψ =
      a.val ≫ (scalarExtensionPresheafIdIso R N).hom := by
    ext U m
    change (ModuleCat.extendScalars (RingHom.id (R.obj.obj U))).map (a.val.app U)
      ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (M.val.obj U) m) =
        (ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (N.val.obj U) (a.val.app U m)
    exact ConcreteCategory.congr_hom ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.naturality
      (a.val.app U)) m
  have hp' : (scalarExtensionPresheafIdIso R M).inv ≫ a.val =
      ψ ≫ (scalarExtensionPresheafIdIso R N).inv := by
    rw [← cancel_epi (scalarExtensionPresheafIdIso R M).hom]
    simp only [← Category.assoc, hp]
    simp
  symm
  change F.map (scalarExtensionPresheafIdIso R M).inv ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.app M ≫ a =
    F.map ψ ≫ F.map (scalarExtensionPresheafIdIso R N).inv ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.app N
  rw [← (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit_naturality a]
  change F.map (scalarExtensionPresheafIdIso R M).inv ≫ F.map a.val ≫ _ = _
  rw [← F.map_comp_assoc, hp', F.map_comp_assoc]

private theorem scalarExtension_quasiIso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{r}} (c : R ⟶ S)
    [(scalarExtension c).Additive]
    {P Q : CochainComplex (Mod J R) ℤ} (s : P ⟶ Q)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (hs : QuasiIso s) :
    QuasiIso (((scalarExtension c).mapHomologicalComplex (.up ℤ)).map s) := by
  let := HasDerivedCategory.standard (Mod J R)
  let := HasDerivedCategory.standard (Mod J S)
  obtain ⟨E, he, hm, hE, hinv, _⟩ := derivedChangeOfRingsIndependentCoefficients c
  let := hE
  have := scalarExtension_additive c
  let e : scalarExtension c ≅ E := NatIso.ofComponents
    (fun M ↦ eqToIso (he M).symm) (by
      intro M N a
      rw [hm]
      simp only [eqToIso.hom, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      rfl)
  let e' := NatIso.mapHomologicalComplex e (.up ℤ)
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e'.app P) (e'.app Q) (e'.hom.naturality s).symm)).2
      (hinv s hP hQ hs)

private theorem kFlat_of_iso_independent
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{r}}
    {P Q : CochainComplex (Mod J R) ℤ}
    (e : P ≅ Q) (hP : P.IsKFlatIndependentCoefficients) :
    Q.IsKFlatIndependentCoefficients := by
  have (I : Type r) : HasColimitsOfShape (Discrete I)
      (PresheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro A hA
  let e' := ((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj A).mapIso e
  exact HomologicalComplex.Acyclic.of_iso (hP A hA) e'

private theorem kFlat_inverseImage_independent
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{r}} {RI : Sheaf JD CommRingCat.{r}}
    (L : Sheaf JC (Type r) ⥤ Sheaf JD (Type r))
    (V : Sheaf JD (Type r) ⥤ Sheaf JC (Type r)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (I : AlgebraicInverseImage L R RI) [I.modules.Additive]
    (P : CochainComplex (Mod JC R) ℤ) (hP : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients
      ((I.modules.mapHomologicalComplex (.up ℤ)).obj P) := by
  have := scalarExtension_additive (𝟙 RI)
  let U := I.modules ⋙ scalarExtension (𝟙 RI)
  have hobj (M) : U.obj M = changeOfRings (𝟙 RI) (I.modules.obj M) := rfl
  have hmap {M N} (a : M ⟶ N) : U.map a = eqToHom (hobj M) ≫
      changeOfRingsHom (𝟙 RI) (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have hk := (isKFlat_ringedToposPullback L V adj I (𝟙 RI) U hobj hmap P hP hf).1
  let e : U ≅ I.modules :=
    Functor.isoWhiskerLeft I.modules (scalarExtensionIdIso RI) ≪≫ I.modules.rightUnitor
  exact kFlat_of_iso_independent
    ((NatIso.mapHomologicalComplex e (.up ℤ)).app P) hk

/-- The resolution comparison witnesses of derived ringed pullback, with the explicit
computation formula and its naturality, identity and composition equations.
Source: Stacks Project, Tag 06YY (blueprint: lem-weil-pbc-ringed-topoi-derived-pullback).
This packages the resolution clauses of the existing node, without new assumptions. -/
structure RingedPullbackResolutionComparisons
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{r}} {S : Sheaf JD CommRingCat.{r}}
    [HasDerivedCategory.{w} (Mod JC R)] [HasDerivedCategory.{w} (Mod JD S)]
    (uStar : Mod JC R ⥤ Mod JD S) [uStar.Additive]
    (LF : DerivedCategory (Mod JC R) ⥤ DerivedCategory (Mod JD S))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) where
  comparison : ∀ {A P : CochainComplex (Mod JC R) ℤ} (p : P ⟶ A),
    P.IsKFlatIndependentCoefficients → (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) →
      QuasiIso p → (LF.obj (DerivedCategory.Q.obj A) ≅
        DerivedCategory.Q.obj ((uStar.mapHomologicalComplex (.up ℤ)).obj P))
  normalization : ∀ {A P : CochainComplex (Mod JC R) ℤ} (p : P ⟶ A)
    (hp : P.IsKFlatIndependentCoefficients) (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n))
    (hq : QuasiIso p),
    (comparison (A := A) (P := P) p hp hf hq).hom =
      inv (LF.map (DerivedCategory.Q.map p)) ≫
        cast (by rfl) (epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
  naturality : ∀ {A A' P P' : CochainComplex (Mod JC R) ℤ}
    (p : P ⟶ A) (p' : P' ⟶ A') (a : P ⟶ P') (b : A ⟶ A')
    (hp : P.IsKFlatIndependentCoefficients) (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n))
    (hq : QuasiIso p)
    (hp' : P'.IsKFlatIndependentCoefficients) (hf' : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R)
      (P'.X n))
    (hq' : QuasiIso p'), p ≫ b = a ≫ p' →
    LF.map (DerivedCategory.Q.map b) ≫ (comparison (A := A') (P := P') p' hp' hf' hq').hom =
      (comparison (A := A) (P := P) p hp hf hq).hom ≫
        DerivedCategory.Q.map ((uStar.mapHomologicalComplex (.up ℤ)).map a)
  map_comparison : ∀ {A P P' : CochainComplex (Mod JC R) ℤ}
    (p : P ⟶ A) (p' : P' ⟶ A) (a : P ⟶ P')
    (hp : P.IsKFlatIndependentCoefficients) (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n))
    (hq : QuasiIso p)
    (hp' : P'.IsKFlatIndependentCoefficients) (hf' : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R)
      (P'.X n))
    (hq' : QuasiIso p'), a ≫ p' = p →
    (comparison (A := A) (P := P) p hp hf hq).inv ≫
      (comparison (A := A) (P := P') p' hp' hf' hq').hom =
        DerivedCategory.Q.map ((uStar.mapHomologicalComplex (.up ℤ)).map a)
  identity : ∀ {A P : CochainComplex (Mod JC R) ℤ} (p : P ⟶ A)
    (hp : P.IsKFlatIndependentCoefficients) (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n))
    (hq : QuasiIso p),
    (comparison (A := A) (P := P) p hp hf hq).inv ≫
      (comparison (A := A) (P := P) p hp hf hq).hom =
        𝟙 (DerivedCategory.Q.obj ((uStar.mapHomologicalComplex (.up ℤ)).obj P))
  composition : ∀ {A P P' P'' : CochainComplex (Mod JC R) ℤ}
    (p : P ⟶ A) (p' : P' ⟶ A) (p'' : P'' ⟶ A)
    (hp : P.IsKFlatIndependentCoefficients) (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n))
    (hq : QuasiIso p)
    (hp' : P'.IsKFlatIndependentCoefficients) (hf' : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R)
      (P'.X n))
    (hq' : QuasiIso p')
    (hp'' : P''.IsKFlatIndependentCoefficients) (hf'' : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R)
      (P''.X n))
    (hq'' : QuasiIso p''),
    ((comparison (A := A) (P := P) p hp hf hq).inv ≫
      (comparison (A := A) (P := P') p' hp' hf' hq').hom) ≫
      ((comparison (A := A) (P := P') p' hp' hf' hq').inv ≫
        (comparison (A := A) (P := P'') p'' hp'' hf'' hq'').hom) =
      (comparison (A := A) (P := P) p hp hf hq).inv ≫
        (comparison (A := A) (P := P'') p'' hp'' hf'' hq'').hom

/-- The exact universal derived ringed pullback, its computation on flat-term K-flat
complexes, and natural resolution comparisons with their identity and composition laws.
Source: Stacks Project, Tag 06YY (blueprint: lem-weil-pbc-ringed-topoi-derived-pullback).
Proof: exact algebraic inverse image and extension of scalars preserve quasi-isomorphisms
between flat-term K-flat complexes, by the K-flat ringed pullback lemma. Flat-term K-flat
resolutions give a resolving class, so localization supplies the universal left derived
functor and its computation transformation. This transformation is invertible on that
class. For a resolution p define alpha(p) by the inverse of LF(Q(p)) followed by the
computation transformation. The resolution square and naturality of that transformation
prove naturality of alpha. For two resolutions use alpha(p) inverse followed by alpha(q);
a compatible chain map gives precisely this comparison. Cancellation proves its identity
and composition laws. These constructions require only relative smallness of the sites,
so the site object and morphism universes need not equal the coefficient universe. -/
theorem ringedTopoiDerivedPullbackIndependent
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{r}} {S RI : Sheaf JD CommRingCat.{r}}
    (uInv : Sheaf JC (Type r) ⥤ Sheaf JD (Type r))
    (uPush : Sheaf JD (Type r) ⥤ Sheaf JC (Type r))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : Mod JC R ⥤
      Mod JD S)
    (hobj : ∀ M : Mod JC R, uStar.obj M = changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : Mod JC R} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (Mod JC R)]
    [HasDerivedCategory.{w} (Mod JD S)] :
    ∃ (LF : DerivedCategory (Mod JC R) ⥤
        DerivedCategory (Mod JD S))
      (epsilon : DerivedCategory.Qh ⋙ LF ⟶
        uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor epsilon
        (HomotopyCategory.quasiIso (Mod JC R) (ComplexShape.up ℤ)) ∧
      (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
      (∀ {P Q : CochainComplex (Mod JC R) ℤ} (s : P ⟶ Q),
        P.IsKFlatIndependentCoefficients → (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) →
        Q.IsKFlatIndependentCoefficients → (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (Q.X n)) →
      QuasiIso s →
          QuasiIso ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) ∧
      (∀ (P : CochainComplex (Mod JC R) ℤ),
        P.IsKFlatIndependentCoefficients → (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) →
          IsIso (epsilon.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) ∧
      Nonempty (RingedPullbackResolutionComparisons uStar LF epsilon) := by
  classical
  let A := Mod JC R
  let B := Mod JD S
  let T := uStar.mapHomologicalComplex (ComplexShape.up ℤ)
  let H := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let F := uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  have hpres : ∀ {P Q : CochainComplex A ℤ} (s : P ⟶ Q),
      P.IsKFlatIndependentCoefficients → (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) →
      Q.IsKFlatIndependentCoefficients → (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (Q.X n)) →
      QuasiIso s → QuasiIso (T.map s) := by
    have := algebraicInverseImage_finiteLimits uInv I
    have : I.modules.Additive := Functor.additive_of_preserves_binary_products I.modules
    have := algebraicInverseImage_epi uInv uPush adj I
    have : I.modules.PreservesHomology :=
      Functor.preservesHomology_of_preservesEpis_and_kernels I.modules
    intro P Q s hp hf hq hqf hs
    have := hs
    have hkP := kFlat_inverseImage_independent uInv uPush adj I P hp hf
    have hkQ := kFlat_inverseImage_independent uInv uPush adj I Q hq hqf
    have := scalarExtension_additive c
    let E := scalarExtension c
    have ht := scalarExtension_quasiIso c
      ((I.modules.mapHomologicalComplex (.up ℤ)).map s) hkP hkQ (by infer_instance)
    let e : uStar ≅ I.modules ⋙ E := NatIso.ofComponents (fun M ↦ eqToIso (hobj M))
      (fun {M N} a ↦ by
        rw [hmap]
        simp only [eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_refl,
          Category.comp_id]
        rfl)
    let e' : T ≅ I.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        E.mapHomologicalComplex (ComplexShape.up ℤ) :=
      NatIso.mapHomologicalComplex e (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (I.modules ⋙ E))
          (ComplexShape.up ℤ)).symm
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (e'.app P) (e'.app Q) (e'.hom.naturality s).symm)).2 ht
  let K : Set (HomotopyCategory A (ComplexShape.up ℤ)) :=
    {X | ∃ P : CochainComplex A ℤ, H.obj P = X ∧
      P.IsKFlatIndependentCoefficients ∧ ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)}
  have hres : ∀ X : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ (X' : HomotopyCategory A (ComplexShape.up ℤ)) (s : X' ⟶ X),
        X' ∈ K ∧ HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s := by
    intro X
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, p, hp, hf, hq, _⟩ := CochainComplex.exists_isKFlatResolutionIndependentCoefficients G
    let := isMonoidal_W_independentCoefficients R
    let := monoidalCategory R
    have hf' (n : ℤ) : IsFlatOnSite (J := JC) (R := R) (P.X n) :=
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X n)).symm (hf n)
    exact ⟨H.obj P, H.map p, ⟨P, rfl, hp, hf'⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hq⟩
  have hinv : ∀ (X X' : HomotopyCategory A (ComplexShape.up ℤ)) (s : X ⟶ X'),
      X ∈ K → X' ∈ K → HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s →
        IsIso (F.map s) := by
    intro X X' s hX hX' hs
    obtain ⟨P, rfl, hp, hf⟩ := hX
    obtain ⟨P', rfl, hp', hf'⟩ := hX'
    obtain ⟨s, rfl⟩ := H.map_surjective s
    have hq := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs
    have ht := hpres s hp hf hp' hf' hq
    change IsIso (DerivedCategory.Qh.map
      ((uStar.mapHomotopyCategory (ComplexShape.up ℤ)).map (H.map s)))
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff (T.map s)).2 ht)
  obtain ⟨_, LF, ε, hLF, hex, hε⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) F K hres hinv
  have hcomp (P : CochainComplex A ℤ) (hp : P.IsKFlatIndependentCoefficients)
      (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) : IsIso (ε.app (H.obj P)) :=
    hε (H.obj P) ⟨P, rfl, hp, hf⟩
  refine ⟨LF, ε, hLF, hex, hpres, hcomp, ?_⟩
  let α : ∀ {G P : CochainComplex A ℤ} (p : P ⟶ G),
      P.IsKFlatIndependentCoefficients →
      (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) → QuasiIso p →
        (LF.obj (DerivedCategory.Q.obj G) ≅ DerivedCategory.Q.obj (T.obj P)) :=
    fun {G P} p hp hf hq ↦ by
      letI := hq
      letI := hcomp P hp hf
      exact (asIso (LF.map (DerivedCategory.Q.map p))).symm ≪≫
        asIso (ε.app (H.obj P))
  have hα {G P : CochainComplex A ℤ} (p : P ⟶ G)
      (hp : P.IsKFlatIndependentCoefficients)
      (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) (hq : QuasiIso p) :
      (α p hp hf hq).hom = inv (LF.map (DerivedCategory.Q.map p)) ≫ ε.app (H.obj P) :=
    rfl
  have hnat {G G' P P' : CochainComplex A ℤ}
      (p : P ⟶ G) (p' : P' ⟶ G') (a : P ⟶ P') (b : G ⟶ G')
      (hp : P.IsKFlatIndependentCoefficients)
      (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) (hq : QuasiIso p)
      (hp' : P'.IsKFlatIndependentCoefficients)
      (hf' : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P'.X n)) (hq' : QuasiIso p')
      (hsq : p ≫ b = a ≫ p') :
      LF.map (DerivedCategory.Q.map b) ≫ (α p' hp' hf' hq').hom =
        (α p hp hf hq).hom ≫ DerivedCategory.Q.map (T.map a) := by
    have := hq
    have := hq'
    rw [hα p hp hf hq, hα p' hp' hf' hq']
    apply (cancel_epi (LF.map (DerivedCategory.Q.map p))).1
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    have hs : LF.map (DerivedCategory.Q.map p) ≫ LF.map (DerivedCategory.Q.map b) =
        LF.map (DerivedCategory.Q.map a) ≫ LF.map (DerivedCategory.Q.map p') := by
      simp only [← Functor.map_comp, hsq]
    rw [← Category.assoc, ← Category.assoc, hs]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact ε.naturality (H.map a)
  refine ⟨{ comparison := α
            normalization := ?_
            naturality := hnat
            map_comparison := ?_
            identity := ?_
            composition := ?_ }⟩
  · intro G P p hp hf hq
    exact hα p hp hf hq
  · intro G P P' p p' a hp hf hq hp' hf' hq' ha
    have h := hnat p p' a (𝟙 G) hp hf hq hp' hf' hq' (by simpa using ha.symm)
    have hid : LF.map (DerivedCategory.Q.map (𝟙 G)) = 𝟙 _ :=
      (congrArg LF.map (DerivedCategory.Q.map_id G)).trans (LF.map_id _)
    rw [hid, Category.id_comp] at h
    change (α p hp hf hq).inv ≫ (α p' hp' hf' hq').hom = _
    rw [h, Iso.inv_hom_id_assoc]
  · intro G P p hp hf hq
    exact (α p hp hf hq).inv_hom_id
  · intro G P P' P'' p p' p'' hp hf hq hp' hf' hq' hp'' hf'' hq''
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

end SheafOfModules
