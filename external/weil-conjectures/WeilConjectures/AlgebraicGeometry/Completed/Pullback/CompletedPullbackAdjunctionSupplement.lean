/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
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
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.AlgebraicGeometry.Exact.ExactPullbackDerivedAdjunction
import WeilConjectures.AlgebraicGeometry.Constant.ConstantDirectImagePreservesComplete

/-!
# Completed pullback is left adjoint to direct image

Source: Stacks Project, `proetale.tex`, Tags 099M and 099N (1), (2), and
`algebraization.tex`, Tag 099K
(blueprint: lem-sp-completed-pullback-adjunction).

All coefficient sheaves, local-completeness predicates and quotient-tower completions
are the constructions of `ConstantCompletionEquivalence`. Positive exponents are n+1.
The existential witnesses below specify geometric module direct image and its total
right derived functor by their underlying maps and universal comparisons. In particular
no preservation or adjunction on complete objects is an assumption.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ConstantCompletion

-- Naturality can be checked through faithful underlying functors, without unfolding
-- the module functors or the chosen lifts of underlying morphisms.
private theorem supplied_homEquiv_naturality
    {C₁ C₂ C₃ D₁ D₂ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category D₁] [Category D₂]
    (I : C₁ ⥤ C₂) (S : C₃ ⥤ C₂) (G : C₃ ⥤ C₁)
    (U : C₁ ⥤ D₁) (V : C₂ ⥤ D₂) [U.Faithful]
    {L : D₁ ⥤ D₂} {R : D₂ ⥤ D₁} (adj : L ⊣ R)
    (eI : I ⋙ V ≅ U ⋙ L) (eP : G ⋙ U ≅ (S ⋙ V) ⋙ R)
    (E : ∀ M H, (I.obj M ⟶ S.obj H) ≃ (M ⟶ G.obj H))
    (hE : ∀ M H a, U.map (E M H a) ≫ eP.hom.app H =
      adj.homEquiv _ _ (eI.inv.app M ≫ V.map a)) :
    (∀ {M N} (a : M ⟶ N) H b, E M H (I.map a ≫ b) = a ≫ E N H b) ∧
    (∀ M {H H'} a (b : H ⟶ H'), E M H' (a ≫ S.map b) = E M H a ≫ G.map b) := by
  constructor
  · intro M N a H b
    apply U.map_injective
    apply (cancel_mono (eP.hom.app H)).mp
    rw [hE, U.map_comp, Category.assoc, hE, V.map_comp]
    have hn : eI.inv.app M ≫ V.map (I.map a) =
        L.map (U.map a) ≫ eI.inv.app N := (eI.inv.naturality a).symm
    rw [← Category.assoc, hn, Category.assoc, adj.homEquiv_naturality_left]
  · intro M H H' a b
    apply U.map_injective
    apply (cancel_mono (eP.hom.app H')).mp
    rw [hE, U.map_comp, Category.assoc]
    have hn : U.map (G.map b) ≫ eP.hom.app H' =
        eP.hom.app H ≫ R.map (V.map (S.map b)) := eP.hom.naturality b
    rw [hn, ← Category.assoc, hE, V.map_comp,
      ← Category.assoc, adj.homEquiv_naturality_right]

open SheafOfModules SheafOfModules.GeometricConstruction in
private theorem supplied_module_add_spec
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (base R)) :
    addSpec M (madd R M) := by
  intro U x
  rfl

open SheafOfModules SheafOfModules.GeometricConstruction in
private theorem supplied_module_smul_spec
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (base R)) :
    smulSpec M (msmul R M) := by
  intro U x
  rfl

-- Restrict the underlying Hom equivalence to linear maps before constructing the adjunction.
-- Keeping this compatibility proof separate avoids unfolding it in the naturality arguments.
open SheafOfModules SheafOfModules.GeometricConstruction in
private theorem supplied_module_linear_iff
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (f : RingedToposMorphism.{u} (C := C) (D := D) (J := J) (K := K) (base A) (base B))
    (RI : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse B RI)
    (c : RI ⟶ A)
    (hc : (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c =
      I.ringUnderlying.inv ≫ f.ringMap)
    (M : SheafOfModules.{u} (base B)) (H : SheafOfModules.{u} (base A))
    (α : (mset RI).obj (I.modules.obj M) ⟶ (mset A).obj H) :
    (∃ a : I.modules.obj M ⟶ (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).map c)).obj H, (mset RI).map a = α) ↔
      ∃ b : M ⟶ f.modules.obj H, (mset B).map b =
        mateIsoEquiv f.adj (I.moduleUnderlying.app M) (f.underlying.app H) α := by
  let _ := f.leftExact
  let _ : PreservesLimits f.direct := f.adj.rightAdjoint_preservesLimits
  let eR := I.ringUnderlying.symm
  let eI := I.moduleUnderlying
  let eP := f.underlying
  have hec : eR.inv ≫ (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c =
      f.ringMap := by
    rw [hc]
    simp only [eR, Iso.symm_inv, Iso.hom_inv_id_assoc]
  let E : ∀ M H, ((mset RI).obj (I.modules.obj M) ⟶ (mset A).obj H) ≃
      ((mset B).obj M ⟶ (mset B).obj (f.modules.obj H)) :=
    fun M H ↦ mateIsoEquiv f.adj (eI.app M) (eP.app H)
  have hLA : f.inverse.map (madd B M) =
      prodComparison f.inverse ((mset B).obj M) ((mset B).obj M) ≫
        prod.map (eI.inv.app M) (eI.inv.app M) ≫ madd RI (I.modules.obj M) ≫
          eI.hom.app M := by
    apply (cancel_mono (eI.inv.app M)).mp
    simp only [Category.assoc, Iso.hom_inv_id_app]
    exact binary_of_graph f.inverse (eI.inv.app M) (eI.inv.app M) (eI.inv.app M)
      (madd B M) (madd RI (I.modules.obj M))
      (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add ((I.modules.obj M).val.obj U) inferInstance x y)
      (supplied_module_add_spec B M) (supplied_module_add_spec RI (I.modules.obj M))
      (fun T x y z hz U t ↦ I.moduleAdd M T x y z hz U t)
  have hLS : f.inverse.map (msmul B M) =
      prodComparison f.inverse (rset B) ((mset B).obj M) ≫
        prod.map eR.inv (eI.inv.app M) ≫ msmul RI (I.modules.obj M) ≫ eI.hom.app M := by
    apply (cancel_mono (eI.inv.app M)).mp
    simp only [Category.assoc, Iso.hom_inv_id_app]
    exact binary_of_graph f.inverse eR.inv (eI.inv.app M) (eI.inv.app M)
      (msmul B M) (msmul RI (I.modules.obj M))
      (fun U x y ↦ @SMul.smul (B.obj.obj U) (M.val.obj U) inferInstance x y)
      (fun U x y ↦ @SMul.smul (RI.obj.obj U) ((I.modules.obj M).val.obj U)
        inferInstance x y)
      (supplied_module_smul_spec B M) (supplied_module_smul_spec RI (I.modules.obj M))
      (fun T a x z hz U t ↦ I.moduleSMul M T a x z hz U t)
  have hRightAdd := (h4_supplied_operations f H).1
  have hRightSmul := (h4_supplied_operations f H).2
  rw [← hec] at hRightSmul
  have hm : f.adj.homEquiv _ _ (eI.inv.app M ≫ α) = E M H α ≫ eP.hom.app H :=
    mateIsoEquiv_equation f.adj (eI.app M) (eP.app H) α
  have hAdd := binary_mate_iso_iff f.adj (eI.app M) (eI.app M) (eI.app M)
    (eP.hom.app H) (eP.hom.app H) (eP.app H) (madd B M)
    (madd RI (I.modules.obj M)) (madd A H) (madd B (f.modules.obj H))
    hLA hRightAdd α α α (E M H α) (E M H α) (E M H α) hm hm hm
  have hSmul := binary_mate_iso_iff f.adj eR (eI.app M) (eI.app M)
    (f.adj.homEquiv _ _ (eR.inv ≫ (sheafCompose J
      (CategoryTheory.forget CommRingCat.{u})).map c))
    (eP.hom.app H) (eP.app H) (msmul B M) (msmul RI (I.modules.obj M))
    (msmul A H) (msmul B (f.modules.obj H)) hLS hRightSmul
    ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c) α α
    (𝟙 (rset B)) (E M H α) (E M H α)
    (by exact (Category.id_comp _).symm) hm hm
  have hSame := linear_iff (𝟙 B) M (f.modules.obj H)
    (madd B M) (madd B (f.modules.obj H)) (msmul B M) (msmul B (f.modules.obj H))
    (supplied_module_add_spec B M) (supplied_module_add_spec B (f.modules.obj H))
    (supplied_module_smul_spec B M) (supplied_module_smul_spec B (f.modules.obj H)) (E M H α)
  exact (linear_iff c (I.modules.obj M) H (madd RI (I.modules.obj M)) (madd A H)
    (msmul RI (I.modules.obj M)) (msmul A H)
    (supplied_module_add_spec RI (I.modules.obj M)) (supplied_module_add_spec A H)
    (supplied_module_smul_spec RI (I.modules.obj M)) (supplied_module_smul_spec A H) α).trans
      ((and_congr hAdd hSmul).trans hSame.symm)

-- Package the restricted equivalence with its underlying map formula, so naturality
-- depends on that formula rather than on the choice of linear lifts.
open SheafOfModules SheafOfModules.GeometricConstruction in
private theorem supplied_module_homEquiv
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (f : RingedToposMorphism.{u} (C := C) (D := D) (J := J) (K := K) (base A) (base B))
    (RI : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse B RI)
    (c : RI ⟶ A)
    (hc : (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c =
      I.ringUnderlying.inv ≫ f.ringMap) :
    ∃ B' : ∀ M H, (I.modules.obj M ⟶ (restrictScalars ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).map c)).obj H) ≃ (M ⟶ f.modules.obj H),
      ∀ M H a, (mset B).map (B' M H a) ≫ f.underlying.hom.app H =
        f.adj.homEquiv _ _ (I.moduleUnderlying.inv.app M ≫ (mset RI).map a) := by
  let eI := I.moduleUnderlying
  let eP := f.underlying
  let E : ∀ M H, ((mset RI).obj (I.modules.obj M) ⟶ (mset A).obj H) ≃
      ((mset B).obj M ⟶ (mset B).obj (f.modules.obj H)) :=
    fun M H ↦ mateIsoEquiv f.adj (eI.app M) (eP.app H)
  have hImage M H (α : (mset RI).obj (I.modules.obj M) ⟶ (mset A).obj H) :=
    supplied_module_linear_iff f RI I c hc M H α
  let B' : ∀ M H, (I.modules.obj M ⟶ (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).map c)).obj H) ≃ (M ⟶ f.modules.obj H) :=
    fun M H ↦ restrictHomEquiv (mset RI) (mset B) (E M H) (hImage M H)
  have hB M H a : (mset B).map (B' M H a) ≫ eP.hom.app H =
      f.adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map a) := by
    rw [restrictHomEquiv_map]
    exact (mateIsoEquiv_equation f.adj (eI.app M) (eP.app H) _).symm
  exact ⟨B', hB⟩

-- Construct the adjunction from the normalized module Hom equivalence.
open SheafOfModules SheafOfModules.GeometricConstruction in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supplied_module_adjunction
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (f : RingedToposMorphism.{u} (C := C) (D := D) (J := J) (K := K) (base A) (base B))
    (RI : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse B RI)
    (c : RI ⟶ A)
    (hc : (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c =
      I.ringUnderlying.inv ≫ f.ringMap) :
    ∃ am : I.modules ⋙ tensorFunctor c ⊣ f.modules,
      ∀ M H k, (underlying B).map (am.homEquiv M H k) ≫ f.underlying.hom.app H =
        f.adj.homEquiv ((underlying B).obj M) ((underlying A).obj H)
          (I.moduleUnderlying.inv.app M ≫ tensorUnit c (I.modules.obj M) ≫
            (underlying A).map k) := by
  let eI := I.moduleUnderlying
  let eP := f.underlying
  obtain ⟨B', hB⟩ := supplied_module_homEquiv f RI I c hc
  obtain ⟨hBL, hBR⟩ := supplied_homEquiv_naturality I.modules
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map c))
    f.modules (mset B) (mset RI) f.adj eI eP B' hB
  let T := I.modules ⋙ tensorFunctor c
  let E' : ∀ M H, (T.obj M ⟶ H) ≃ (M ⟶ f.modules.obj H) :=
    fun M H ↦ ((tensorAdjunction c).homEquiv (I.modules.obj M) H).trans (B' M H)
  have hEL {M N} (a : M ⟶ N) H (b : T.obj N ⟶ H) :
      E' M H (T.map a ≫ b) = a ≫ E' N H b := by
    dsimp only [E', Equiv.trans_apply, T, Functor.comp_map]
    change B' M H ((tensorAdjunction c).homEquiv (I.modules.obj M) H
      ((tensorFunctor c).map (I.modules.map a) ≫ b)) = _
    rw [(tensorAdjunction c).homEquiv_naturality_left, hBL]
    rfl
  let am : T ⊣ f.modules := Adjunction.mkOfHomEquiv {
    homEquiv := E'
    homEquiv_naturality_left_symm := by
      intro M N H a b
      apply (E' M H).injective
      rw [Equiv.apply_symm_apply, hEL, Equiv.apply_symm_apply]
    homEquiv_naturality_right := by
      intro M H H' a b
      dsimp only [E', Equiv.trans_apply]
      change B' M H' ((tensorAdjunction c).homEquiv (I.modules.obj M) H' (a ≫ b)) = _
      rw [(tensorAdjunction c).homEquiv_naturality_right]
      exact hBR M ((tensorAdjunction c).homEquiv (I.modules.obj M) H a) b }
  refine ⟨am, ?_⟩
  intro M H k
  dsimp only [am]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  change (underlying B).map (B' M H
    ((tensorAdjunction c).homEquiv (I.modules.obj M) H k)) ≫ eP.hom.app H = _
  rw [hB]
  exact congrArg (f.adj.homEquiv _ _)
    (congrArg (eI.inv.app M ≫ ·) (tensorAdjunction_underlying c (I.modules.obj M) H k))

open SheafOfModules SheafOfModules.GeometricConstruction in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem module_adjunction_exists
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    {L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)}
    (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (F : InverseImageData L)
    {R : Sheaf JC CommRingCat.{u}} {S : Sheaf JD CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) :
    ∃ (G : Mod S ⥤+ Mod R)
      (eG : G.obj ⋙ underlying R ≅ underlying S ⋙ V) (aM : pull F c ⊣ G.obj),
      ∀ M N f, (underlying R).map (aM.homEquiv M N f) ≫ eG.hom.app N =
        adj.homEquiv ((underlying R).obj M) ((underlying S).obj N)
          (pullInsertion F c M ≫ (underlying S).map f) := by
  let AI := F.algebra R
  let d : RingedToposMorphism.RingData (siteModuleRings S) (siteModuleRings R) :=
    { inverse := L
      direct := V
      adj := adj
      leftExact := inferInstance
      ringMap := AI.ringUnderlying.hom ≫ (sheafCompose JD (forget CommRingCat)).map c
      ring_zero := by
        intro T z hz U t
        change (c.hom.app U).hom
          (AI.ringUnderlying.hom.hom.app U ((L.map z).hom.app U t)) = 0
        exact (congrArg (fun a ↦ (c.hom.app U).hom a)
          (AI.ringZero T z hz U t)).trans (map_zero _)
      ring_one := by
        intro T z hz U t
        change (c.hom.app U).hom
          (AI.ringUnderlying.hom.hom.app U ((L.map z).hom.app U t)) = 1
        exact (congrArg (fun a ↦ (c.hom.app U).hom a)
          (AI.ringOne T z hz U t)).trans (map_one _)
      ring_add := by
        intro T x y z hz U t
        change (c.hom.app U).hom
          (AI.ringUnderlying.hom.hom.app U ((L.map z).hom.app U t)) =
          (c.hom.app U).hom
              (AI.ringUnderlying.hom.hom.app U ((L.map x).hom.app U t)) +
            (c.hom.app U).hom
              (AI.ringUnderlying.hom.hom.app U ((L.map y).hom.app U t))
        exact (congrArg (fun a ↦ (c.hom.app U).hom a)
          (AI.ringAdd T x y z hz U t)).trans (map_add _ _ _)
      ring_mul := by
        intro T x y z hz U t
        change (c.hom.app U).hom
          (AI.ringUnderlying.hom.hom.app U ((L.map z).hom.app U t)) =
          (c.hom.app U).hom
              (AI.ringUnderlying.hom.hom.app U ((L.map x).hom.app U t)) *
            (c.hom.app U).hom
              (AI.ringUnderlying.hom.hom.app U ((L.map y).hom.app U t))
        exact (congrArg (fun a ↦ (c.hom.app U).hom a)
          (AI.ringMul T x y z hz U t)).trans (map_mul _ _ _) }
  obtain ⟨md⟩ := ringData_inducedModules S R d
  let f := d.withModules md
  let : f.modules.Additive := f.additive
  have hc : (sheafCompose JD (forget CommRingCat)).map c =
      AI.ringUnderlying.inv ≫ f.ringMap := by
    change _ = AI.ringUnderlying.inv ≫
      (AI.ringUnderlying.hom ≫ (sheafCompose JD (forget CommRingCat)).map c)
    simp only [Iso.inv_hom_id_assoc]
  obtain ⟨aM, haM⟩ := supplied_module_adjunction f (F.rings.obj R) AI c hc
  refine ⟨AdditiveFunctor.of f.modules, f.underlying, aM, ?_⟩
  intro M N k
  refine (haM M N k).trans ?_
  have hq : insertion c (AI.modules.obj M) = tensorUnit c (AI.modules.obj M) := by
    ext U m
    exact ((insertion_existsUnique c (AI.modules.obj M)).exists.choose_spec U m).trans
      (tensorUnit_apply c (AI.modules.obj M) U m).symm
  dsimp only [pullInsertion]
  rw [hq, Category.assoc]
  rfl

open SheafOfModules SheafOfModules.GeometricConstruction in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictScalars_equivalence
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (c : R ≅ S) :
    (restrictScalars.{u} c.hom).IsEquivalence := by
  let ec : C ≌ C := Equivalence.refl
  have : ec.functor.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  have : ec.inverse.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let e := pushforwardPushforwardEquivalence (J := J) (K := J)
    ec c.hom c.inv
    (by
      ext U x
      dsimp [ec, Equivalence.refl]
      simp only [Functor.map_id]
      exact congrArg (fun f : S ⟶ S ↦ f.hom.app U x) c.inv_hom_id.symm)
    (by
      ext U x
      dsimp [ec, Equivalence.refl]
      simp only [Functor.map_id]
      exact congrArg (fun f : R ⟶ R ↦ f.hom.app U x) c.hom_inv_id)
  have h : restrictScalars.{u} c.hom = e.functor := by rfl
  rw [h]
  exact e.isEquivalence_functor

open SheafOfModules SheafOfModules.GeometricConstruction in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pull_finiteLimits_of_isIso
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    {L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)} [PreservesFiniteLimits L]
    (F : InverseImageData L)
    {R : Sheaf JC CommRingCat.{u}} {S : Sheaf JD CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) [IsIso c] : PreservesFiniteLimits (pull F c) := by
  let r := sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})
  have : (restriction c).IsEquivalence :=
    restrictScalars_equivalence (r.mapIso (asIso c))
  have := (tensorAdjunction c).isEquivalence_left_of_isEquivalence_right
  have := algebraicInverseImage_finiteLimits L (F.algebra R)
  exact comp_preservesFiniteLimits (F.algebra R).modules (tensorFunctor c)

open SheafOfModules SheafOfModules.GeometricConstruction in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reflector_of_bijective
    {B : Type*} [Category B] (P : ObjectProperty B) (T : B ⥤ B)
    (η : 𝟭 B ⟶ T) (hT : ∀ X, P (T.obj X))
    (hbij : ∀ X Y, P Y → Function.Bijective (fun f : T.obj X ⟶ Y ↦ η.app X ≫ f)) :
    ∃ a : ObjectProperty.lift P T hT ⊣ P.ι,
      ∀ X Y f, a.homEquiv X Y f = η.app X ≫ f.hom := by
  classical
  let E : ∀ X (Y : P.FullSubcategory),
      ((ObjectProperty.lift P T hT).obj X ⟶ Y) ≃ (X ⟶ Y.obj) :=
    fun X Y ↦ P.fullyFaithfulι.homEquiv.trans
      (Equiv.ofBijective (fun f ↦ η.app X ≫ f) (hbij X Y.obj Y.property))
  have hEL {X X' : B} (a : X ⟶ X') (Y : P.FullSubcategory)
      (f : (ObjectProperty.lift P T hT).obj X' ⟶ Y) :
      E X Y ((ObjectProperty.lift P T hT).map a ≫ f) = a ≫ E X' Y f := by
    change η.app X ≫ T.map a ≫ f.hom = a ≫ η.app X' ≫ f.hom
    rw [← Category.assoc, ← η.naturality]
    simp only [Category.assoc, Functor.id_map]
  let core : Adjunction.CoreHomEquiv (ObjectProperty.lift P T hT) P.ι :=
    { homEquiv := E
      homEquiv_naturality_left_symm := by
        intro X X' Y a g
        apply (E X Y).injective
        calc
          _ = a ≫ g := (E X Y).apply_symm_apply _
          _ = _ := by
            rw [hEL]
            exact congrArg (fun t ↦ a ≫ t) ((E X' Y).apply_symm_apply g).symm
      homEquiv_naturality_right := by
        intro X Y Y' f g
        change η.app X ≫ f.hom ≫ g.hom = (η.app X ≫ f.hom) ≫ g.hom
        simp only [Category.assoc] }
  refine ⟨Adjunction.mkOfHomEquiv core, ?_⟩
  intro X Y f
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

open SheafOfModules SheafOfModules.GeometricConstruction in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem complete_adjunction
    {B D' : Type*} [Category B] [Category D']
    (P : ObjectProperty B) (P' : ObjectProperty D')
    (F : B ⥤ D') (G : D' ⥤ B) (a : F ⊣ G)
    (T : D' ⥤ D') (η : 𝟭 D' ⟶ T) (hT : ∀ X, P' (T.obj X))
    (hG : ∀ Y, P' Y → P (G.obj Y))
    (aT : ObjectProperty.lift P' T hT ⊣ P'.ι)
    (haT : ∀ X Y f, aT.homEquiv X Y f = η.app X ≫ f.hom) :
    ∃ a' : ObjectProperty.lift P' (P.ι ⋙ F ⋙ T) (fun X ↦ hT (F.obj X.obj)) ⊣
        ObjectProperty.lift P (P'.ι ⋙ G) (fun Y ↦ hG Y.obj Y.property),
      ∀ M N (f : T.obj (F.obj M.obj) ⟶ N.obj),
        (a'.homEquiv M N (ObjectProperty.homMk f)).hom =
          a.homEquiv M.obj N.obj (η.app (F.obj M.obj) ≫ f) := by
  let LF := ObjectProperty.lift P' (P.ι ⋙ F ⋙ T) (fun X ↦ hT (F.obj X.obj))
  let RG := ObjectProperty.lift P (P'.ι ⋙ G) (fun Y ↦ hG Y.obj Y.property)
  let E : ∀ M N, (LF.obj M ⟶ N) ≃ (M ⟶ RG.obj N) :=
    fun M N ↦ (aT.homEquiv (F.obj M.obj) N).trans
      ((a.homEquiv M.obj N.obj).trans (P.fullyFaithfulι.homEquiv (X := M) (Y := RG.obj N)).symm)
  have hE (M : P.FullSubcategory) (N : P'.FullSubcategory) (f : LF.obj M ⟶ N) :
      (E M N f).hom = a.homEquiv M.obj N.obj (η.app (F.obj M.obj) ≫ f.hom) := by
    exact congrArg (a.homEquiv M.obj N.obj) (haT _ _ f)
  have hEL {M M' : P.FullSubcategory} (b : M ⟶ M') (N : P'.FullSubcategory)
      (f : LF.obj M' ⟶ N) : E M N (LF.map b ≫ f) = b ≫ E M' N f := by
    apply ObjectProperty.hom_ext
    change (E M N (LF.map b ≫ f)).hom = b.hom ≫ (E M' N f).hom
    rw [hE, hE]
    change a.homEquiv _ _ (η.app (F.obj M.obj) ≫ T.map (F.map b.hom) ≫ f.hom) = _
    rw [← Category.assoc, ← η.naturality, Functor.id_map, Category.assoc,
      a.homEquiv_naturality_left]
  let core : Adjunction.CoreHomEquiv LF RG :=
    { homEquiv := E
      homEquiv_naturality_left_symm := by
        intro M M' N b g
        apply (E M N).injective
        simp only [hEL, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro M N N' f b
        apply ObjectProperty.hom_ext
        change (E M N' (f ≫ b)).hom = (E M N f).hom ≫ G.map b.hom
        rw [hE, hE]
        change a.homEquiv _ _ (η.app (F.obj M.obj) ≫ f.hom ≫ b.hom) =
          a.homEquiv _ _ (η.app (F.obj M.obj) ≫ f.hom) ≫ G.map b.hom
        rw [← Category.assoc, a.homEquiv_naturality_right] }
  refine ⟨Adjunction.mkOfHomEquiv core, ?_⟩
  intro M N f
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  exact hE M N (ObjectProperty.homMk f)

end CategoryTheory.ConstantCompletion
