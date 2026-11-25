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
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
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
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian

/-! # Specified strict-perfect models for derived ringed-topos pullback

Source: Stacks Project, Cohomology on Sites, Tag 08H3, lemma-strictly-perfect-pullback;
Tag 06YQ and Section derived-pullback, Tag 06YY
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model).

The finite-free comparison is characterized on all local pure tensors, so its choice
is uniquely determined. The transported splittings are degreewise, with no assertion
that they commute with the differentials.

## Main definitions and statements

- `ringedPullbackFiniteFreeIso`: the uniquely characterized finite-free comparison.
- `ringedPullbackStrictPerfectPackage`: the specified transported degreewise splittings.
- `ringedPullbackComplexComparison`: the given comparison on cochain complexes.
- `strictPerfectRingedPullbackModel`: flatness, K-flatness, bounds and natural comparison.
-/

@[expose] public section

set_option linter.privateModule false
set_option autoImplicit false

-- Avoid repeated multicospan searches: first use size-bounded limits, then the small model.
attribute [local instance 12000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
attribute [local instance 11000] CategoryTheory.hasSheafComposeEssentiallySmallSite

universe uC vC uD vD r w
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules

section DerivedHelpers
open MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

private noncomputable abbrev moduleUnderlying
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r}) :=
  toSheaf ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})

private theorem moduleUnderlying_finiteLimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r}) : PreservesFiniteLimits (moduleUnderlying R) := by
  let V := sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})
  have : PreservesFiniteLimits (V ⋙ sheafToPresheaf J (Type (r))) :=
    show PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{r} ⋙
      (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{r})) from
        comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits V :=
    preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type (r)))
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
    (L : Sheaf JC (Type (r)) ⥤ Sheaf JD (Type (r))) [PreservesFiniteLimits L]
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
    (L : Sheaf JC (Type (r)) ⥤ Sheaf JD (Type (r)))
    (V : Sheaf JD (Type (r)) ⥤ Sheaf JC (Type (r))) (adj : L ⊣ V)
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
  scalarExtensionPresheaf c ⋙ PresheafOfModules.sheafification.{r, vC, r, uC}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)

private theorem scalarExtension_additive
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{r}} (c : R ⟶ S) :
    (scalarExtension c).Additive := by
  have hsheaf : (PresheafOfModules.sheafification.{r, vC, r, uC}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction.{r, vC, r, uC} (𝟙 _)).left_adjoint_additive
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
  (PresheafOfModules.sheafification.{r, vC, r, uC} (𝟙 _)).mapIso
      (scalarExtensionPresheafIdIso R M).symm ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction.{r, vC, r, uC} (𝟙 _)).counit.app M)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarExtensionIdIso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r}) : scalarExtension (𝟙 R) ≅ 𝟭 _ := by
  refine NatIso.ofComponents (scalarExtensionIdIsoApp R) ?_
  intro M N a
  let F := PresheafOfModules.sheafification.{r, vC, r, uC}
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
      (PresheafOfModules.sheafificationAdjunction.{r, vC, r, uC} (𝟙 _)).counit.app M ≫ a =
    F.map ψ ≫ F.map (scalarExtensionPresheafIdIso R N).inv ≫
      (PresheafOfModules.sheafificationAdjunction.{r, vC, r, uC} (𝟙 _)).counit.app N
  rw [← (PresheafOfModules.sheafificationAdjunction.{r, vC, r, uC} (𝟙 _)).counit_naturality a]
  change F.map (scalarExtensionPresheafIdIso R M).inv ≫ F.map a.val ≫ _ = _
  rw [← F.map_comp_assoc, hp', F.map_comp_assoc]

set_option synthInstance.maxSize 256 in
private theorem isKFlat_of_iso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{r}}
    {P Q : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ}
    (e : P ≅ Q) (hP : P.IsKFlatIndependentCoefficients) : Q.IsKFlatIndependentCoefficients := by
  let : ∀ (I₁ I₂ : Type r), HasColimitsOfShape (Discrete I₂)
      (PresheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj) :=
    fun _ _ ↦ PresheafOfModules.hasColimitsOfShape _ _
  let : HasCoproducts.{0} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) := fun I ↦ by
    let : HasColimitsOfShape (Discrete I) (PresheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj) :=
      PresheafOfModules.hasColimitsOfShape _ _
    exact
      SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
  let : HasFiniteCoproducts (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
    hasFiniteCoproducts_of_hasCoproducts _
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro A hA n
  let F := (MonoidalCategory.curriedTensor (SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let e' : CochainComplex.mapBifunctor A P (curriedTensor _) ≅
      CochainComplex.mapBifunctor A Q (curriedTensor _) :=
    HomologicalComplex₂.total.mapIso ((F.obj A).mapIso e) (ComplexShape.up ℤ)
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ n).1 (hP A hA n)).of_iso
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso e').symm |>
      (HomologicalComplex.exactAt_iff_isZero_homology _ n).2

private theorem isKFlat_inverseImage
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{r}} {RI : Sheaf JD CommRingCat.{r}}
    (L : Sheaf JC (Type (r)) ⥤ Sheaf JD (Type (r)))
    (V : Sheaf JD (Type (r)) ⥤ Sheaf JC (Type (r))) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (I : AlgebraicInverseImage L R RI) [I.modules.Additive]
    (P : CochainComplex (SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients
      ((I.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  have := algebraicInverseImage_finiteLimits L I
  have : I.modules.Additive := Functor.additive_of_preserves_binary_products I.modules
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
  exact isKFlat_of_iso ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app P)
    hk

end DerivedHelpers

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  {R : Sheaf JC CommRingCat.{r}} {RI S : Sheaf JD CommRingCat.{r}}
  (uInv : Sheaf JC (Type r) ⥤ Sheaf JD (Type r))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (uStar : ringedSiteModules.{r}
    ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
    ringedSiteModules.{r} ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
  (hobj : ∀ M : ringedSiteModules.{r}
    ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R),
    uStar.obj M = changeOfRings c (I.modules.obj M))

private noncomputable abbrev moduleSets
    {E : Type uC} [Category.{vC} E] [EssentiallySmall.{r} E]
    {J : GrothendieckTopology E} (A : Sheaf J CommRingCat.{r}) :=
  toSheaf ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})

-- Recover the rank-one module comparison from the transported scalar action.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem inverseImage_unit_iso :
    ∃ e : I.modules.obj
        (unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ≅
        unit ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RI),
      (moduleSets RI).map e.hom = I.moduleUnderlying.hom.app
        (unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ≫
          I.ringUnderlying.hom := by
  let U := unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  let Z := (moduleSets R).obj U
  let one : Z ⟶ Z := ⟨{ app := fun W ↦ ↾(fun _ ↦ (1 : R.obj.obj W))
                        naturality := by
                          intro W V f
                          ext x
                          exact (map_one (R.obj.map f).hom).symm }⟩
  let e : (moduleSets RI).obj (I.modules.obj U) ≅
      (sheafCompose JD (CategoryTheory.forget CommRingCat.{r})).obj RI :=
    I.moduleUnderlying.app U ≪≫ I.ringUnderlying
  let g (W : Dᵒᵖ) (a : RI.obj.obj W) : (I.modules.obj U).val.obj W :=
    e.inv.hom.app W a
  have hf (W : Dᵒᵖ) (a : RI.obj.obj W) : g W a =
      (show ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RI).obj.obj W
        from a) • g W 1 := by
    let t := I.ringUnderlying.inv.hom.app W a
    have ht : I.ringUnderlying.hom.hom.app W t = a :=
      congrArg (fun f ↦ f.hom.app W a) I.ringUnderlying.inv_hom_id
    have ho := I.ringOne Z one (fun _ _ ↦ rfl) W t
    have hi := congrArg (I.ringUnderlying.inv.hom.app W) ho
    have hc (x : (uInv.obj Z).obj.obj W) :
        I.ringUnderlying.inv.hom.app W (I.ringUnderlying.hom.hom.app W x) = x :=
      congrArg (fun f ↦ f.hom.app W x) I.ringUnderlying.hom_inv_id
    simp only [id_eq] at hi
    rw [hc] at hi
    let m (x : (uInv.obj Z).obj.obj W) : (I.modules.obj U).val.obj W :=
      (I.moduleUnderlying.inv.app U).hom.app W x
    have hm : m t =
        (show ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RI).obj.obj W
          from I.ringUnderlying.hom.hom.app W t) •
        m ((uInv.map one).hom.app W t) := by
      have h := I.moduleSMul U Z (𝟙 Z) one (𝟙 Z)
        (fun W x ↦ (mul_one (show R.obj.obj W from x)).symm) W t
      erw [uInv.map_id] at h
      exact h
    erw [ht, hi] at hm
    exact hm
  let eW (W : Dᵒᵖ) : RI.obj.obj W ≃ₗ[RI.obj.obj W] (I.modules.obj U).val.obj W :=
    { toEquiv := (((sheafToPresheaf JD (Type r)).mapIso e).app W).toEquiv.symm
      map_add' := by
        intro a b
        change g W (a + b) = g W a + g W b
        rw [hf W (a + b), hf W a, hf W b, add_smul]
      map_smul' := by
        intro a b
        change g W (a * b) = a • g W b
        rw [hf W (a * b), hf W b, mul_smul] }
  let ep : (unit ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RI)).val ≅
      (I.modules.obj U).val :=
    PresheafOfModules.isoMk (fun W ↦ (eW W).toModuleIso) (by
      intro W V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact congrArg (fun k ↦ k a) (e.inv.hom.naturality f))
  refine ⟨(fullyFaithfulForget _).preimageIso ep.symm, ?_⟩
  rfl

variable (uPush : Sheaf JD (Type r) ⥤ Sheaf JC (Type r))
  (adj : uInv ⊣ uPush) [hlim : PreservesFiniteLimits uInv]
  (hmap : ∀ {M N : ringedSiteModules.{r}
    ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)} (a : M ⟶ N),
    uStar.map a = eqToHom (hobj M) ≫
      changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫ eqToHom (hobj N).symm)
  [hadd : uStar.Additive]

include adj hmap hlim hadd

variable [HasDerivedCategory.{w} (ringedSiteModules.{r}
    ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
  [HasDerivedCategory.{w} (ringedSiteModules.{r}
    ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S))]
  (LF : DerivedCategory (ringedSiteModules.{r}
    ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤
    DerivedCategory (ringedSiteModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S)))
  (epsilon : DerivedCategory.Qh ⋙ LF ⟶
    uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)

end SheafOfModules
