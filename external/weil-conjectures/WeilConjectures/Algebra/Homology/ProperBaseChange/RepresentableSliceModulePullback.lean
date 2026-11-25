/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Sheaf.RingedSheafSliceConstruction
public import WeilConjectures.Algebra.Homology.ProperBaseChange.OrdinaryRingedToposPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.CategoryTheory.ProperBaseChange.GeometricRingedPullbackSlice
import all WeilConjectures.CategoryTheory.ProperBaseChange.ElementRestrictionHom
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
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
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
import all WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections

/-! Pullback of modules from a represented object slice. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

-- The module comparisons involve several nested element sites.
set_option maxRecDepth 4000 in
/-- Pullback from the represented source slice, with its colimit and unit comparisons.

Source: Stacks Project, Modules on Sites, Tags 03D2, 03DF and 04IF;
Sites, Tag 0791.
(blueprint: lem-weil-pbc-representable-slice-module-pullback).

Proof: Write H for the sheafified representable of U. Transport modules from D/U
through the fibre equivalence Sh(D/U) = Sh(D)/H. The ring becomes the restriction
of B and the transported module M.over U becomes elementModulePullback B H M.
This equivalence preserves colimits and sends the rank-one module to the rank-one
module. Localize f at H using the geometric ringed slice morphism. Pullback of
modules there is left adjoint to its module direct image: the inverse-image
adjunction restricts to linear maps and scalar extension is tensor-adjoint to
restriction of scalars. Thus the composite preserves colimits. Its value on the
rank-one module is the rank-one module by S tensor_R R = S, with inverse s to
s tensor 1. The geometric module slice comparison identifies its value on
M.over U with the localization of ordinaryRingedToposPullback I c M. This
comparison uses hc to identify the structural coefficient map. No finite-type
hypothesis, site functor representing f, or subcanonicity is used. -/
theorem representableSliceModulePullback_exists
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (RI : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse B RI)
    (c : RI ⟶ A)
    (hc : I.ringUnderlying.hom ≫
      (sheafCompose J (CategoryTheory.forget CommRingCat)).map c = f.ringMap)
    (U : D) :
    ∃ F : ringedSiteModules.{u}
        (((sheafCompose K (forget₂ CommRingCat RingCat)).obj B).over U) ⥤
      ringedSiteModules.{u} (elementRing
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
        (f.inverse.obj ((presheafToSheaf K (Type u)).obj (yoneda.obj U)))),
      PreservesColimitsOfSize.{u, u} F ∧
      Nonempty (unit (elementRing
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
        (f.inverse.obj ((presheafToSheaf K (Type u)).obj (yoneda.obj U)))) ≅
        F.obj (unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj B).over U))) ∧
      ∀ M : ringedSiteModules.{u}
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B),
        Nonempty (F.obj (M.over U) ≅
          (elementModulePullback ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
            (f.inverse.obj ((presheafToSheaf K (Type u)).obj (yoneda.obj U)))).obj
              (ordinaryRingedToposPullback I c M)) := by
  let H := (presheafToSheaf K (Type u)).obj (yoneda.obj U)
  obtain ⟨E, ⟨k⟩⟩ := CategoryTheory.ordinarySliceComparison B U
  obtain ⟨y⟩ := ringed_sheaf_slice_adjunction (localCoefficientRings B) H
  obtain ⟨x⟩ := ringed_sheaf_slice_adjunction (localCoefficientRings A) (f.inverse.obj H)
  obtain ⟨fA, slice, a, ha, hr, hp⟩ := geometric_ringed_pullback_slice A B f H y x
  obtain ⟨RIA, IA, ca, hca, e, hn, ht⟩ := hp RI I c hc
  let T := IA.modules ⋙ tensorFunctor ca
  have hca' := congrArg (IA.ringUnderlying.inv ≫ ·) hca
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at hca'
  obtain ⟨adj⟩ := supplied_adjunction fA RIA IA ca hca'
  let : PreservesColimitsOfSize.{u, u} T := adj.leftAdjoint_preservesColimits
  let F := E.modules.functor ⋙ T
  obtain ⟨eI, heI⟩ := inverseImage_unit_iso (presentationElementRing B H) RIA fA.inverse IA
  obtain ⟨eS, heS⟩ := scalarExtension_unit_iso
    (presentationElementRing A (f.inverse.obj H)) RIA ca
  let eT := (tensorFunctor ca).mapIso eI.symm ≪≫ eS
  refine ⟨F, inferInstance, ⟨(T.mapIso E.forwardUnit ≪≫ eT).symm⟩, ?_⟩
  intro M
  exact ⟨T.mapIso (k.app M) ≪≫ e M⟩

end SheafOfModules
