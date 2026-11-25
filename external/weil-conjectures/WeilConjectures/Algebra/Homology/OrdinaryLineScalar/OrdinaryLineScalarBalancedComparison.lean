/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarData
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
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
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

/-! # Balanced ordinary scalar and line tensor

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 0G7E and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
universe t a w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
namespace SheafOfModules.OrdinaryLineScalar
attribute [local instance] modulesCategory modulesAbelian monoidalCategory
attribute [local implicit_reducible] monoidalCategory
variable {X : Scheme.{t}} [EssentiallySmall.{max a (t + 1)} X.ProEt]
  [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
    HasDerivedCategory.{w} (Modules.{t, a} X R)]
local notation "𝒬[" R "]" => (DerivedCategory.Q (C := Modules X R))
variable {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}

attribute [local irreducible] monoidalCategory LineUnbounded.derived signedLinePower
  scalarTensorPower

private theorem scalar_eq_sectionTensor (α : R ⟶ S)
    (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (M : Modules.{t, a} X R) (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    scalar p M U s x = SuccessiveDerivedQuotient.sectionTensor p M U s x := by
  unfold scalar
  rfl

private def extensionObjectIso (α : R ⟶ S)
    (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α) (M : Modules.{t, a} X R) :
    p.ordinary.obj M ≅ changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α M :=
  eqToIso (p.obj_eq M) ≪≫ ScalarHomOrdinary.extensionIso α M

private theorem extensionObjectIso_scalar (α : R ⟶ S)
    (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (M : Modules.{t, a} X R) (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (extensionObjectIso α p M).hom.val.app U (scalar p M U s x) =
      scalarExtensionSection α M U s x := by
  have hs : scalarExtensionSection α M U s x =
      s • scalarExtensionSection α M U 1 x := by
    simpa only [mul_one] using (scalarExtensionSection_smul α M U s 1 x).symm
  unfold scalar
  rw [hs, (eqToHom (p.obj_eq M).symm).val.app U |>.hom.map_smul,
    (extensionObjectIso α p M).hom.val.app U |>.hom.map_smul]
  congr 1
  change (ScalarHomOrdinary.extensionIso α M).hom.val.app U
    ((eqToHom (p.obj_eq M)).val.app U
      ((eqToHom (p.obj_eq M).symm).val.app U _)) = _
  have h := congrArg (fun f ↦ f.val.app U
    (scalarExtensionSection α M U 1 x)) (eqToIso (p.obj_eq M)).inv_hom_id
  change (eqToHom (p.obj_eq M)).val.app U
    ((eqToHom (p.obj_eq M).symm).val.app U _) = _ at h
  rw [h]
  exact ScalarHomOrdinary.extensionIso_unit α M U x

private theorem extensionObjectIso_inv_scalar (α : R ⟶ S)
    (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (M : Modules.{t, a} X R) (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (extensionObjectIso α p M).inv.val.app U (scalarExtensionSection α M U s x) =
      scalar p M U s x := by
  rw [← extensionObjectIso_scalar α p M U s x]
  exact congrArg (fun f ↦ f.val.app U (scalar p M U s x))
    (extensionObjectIso α p M).hom_inv_id

private def balancedComponent (α : R ⟶ S)
    (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (c : ScalarExtensionTensorCore.{t + 1, t, max a (t + 1)}
      (J := Scheme.ProEt.topology X) R S α)
    (A : Modules.{t, a} X R) (D : Modules.{t, a} X S)
    (b : changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α A ≅ D) (M : Modules.{t, a} X R) :
    p.ordinary.obj ((monoidalCategory R).tensorObj M A) ≅
      (monoidalCategory S).tensorObj (p.ordinary.obj M) D :=
  extensionObjectIso α p _ ≪≫
    (ScalarHomOrdinary.extensionFunctor α).mapIso
      (ScalarHomOrdinary.tensorIsoSite R M A) ≪≫
    c.tensorComparison M A ≪≫
    (ScalarHomOrdinary.tensorIsoSite S
      (changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α M)
      (changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α A)).symm ≪≫
    @tensorIso _ _ (monoidalCategory S) _ _ _ _ (extensionObjectIso α p M).symm b

private theorem balancedComponent_hom (α : R ⟶ S)
    (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (c : ScalarExtensionTensorCore.{t + 1, t, max a (t + 1)}
      (J := Scheme.ProEt.topology X) R S α)
    (A : Modules.{t, a} X R) (D : Modules.{t, a} X S)
    (b : changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α A ≅ D) (M : Modules.{t, a} X R)
    (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) (y : A.val.obj U) :
    (balancedComponent α p c A D b M).hom.val.app U
      (scalar p ((monoidalCategory R).tensorObj M A) U s
        (ScalarHomOrdinary.pure R M A U x y)) =
    ScalarHomOrdinary.pure S (p.ordinary.obj M) D U (scalar p M U s x)
      (b.hom.val.app U (scalarExtensionSection α A U 1 y)) := by
  change ((monoidalCategory S).tensorHom (extensionObjectIso α p M).inv b.hom).val.app U
    ((ScalarHomOrdinary.tensorIsoSite S _ _).inv.val.app U
      ((c.tensorComparison M A).hom.val.app U
        ((changeOfRingsHomOfUniverses α _
          (ScalarHomOrdinary.tensorIsoSite R M A).hom).val.app U
          ((extensionObjectIso α p _).hom.val.app U _)))) = _
  rw [extensionObjectIso_scalar α p _ U s _,
    scalarExtension_map_tmul α (ScalarHomOrdinary.tensorIsoSite R M A).hom U s
      (ScalarHomOrdinary.pure R M A U x y),
    ScalarHomOrdinary.tensorIsoSite_pure R M A U x y, c.tensor_tmul M A U s x y,
    ScalarHomOrdinary.tensorIsoSite_inv_pure S _ _ U _ _,
    ScalarHomOrdinary.pure_map S (extensionObjectIso α p M).inv b.hom U _ _,
    extensionObjectIso_inv_scalar α p M U s x]

private theorem pure_smul_first (A : Sheaf (Scheme.ProEt.topology X)
    CommRingCat.{max a (t + 1)}) (M N : Modules.{t, a} X A)
    (U : X.ProEtᵒᵖ) (s : A.obj.obj U) (x : M.val.obj U) (y : N.val.obj U) :
    ScalarHomOrdinary.pure A M N U (s • x) y =
      s • ScalarHomOrdinary.pure A M N U x y := by
  unfold ScalarHomOrdinary.pure
  change (tensorObjIsoSheafification M N).inv.val.app U
    ((((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
      (M.val ⊗ N.val)).app U) (s • (x ⊗ₜ[A.obj.obj U] y))) = _
  rw [(((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
    (M.val ⊗ N.val)).app U).hom.map_smul]
  exact ((tensorObjIsoSheafification M N).inv.val.app U).hom.map_smul s _

private theorem pure_smul_second (A : Sheaf (Scheme.ProEt.topology X)
    CommRingCat.{max a (t + 1)}) (M N : Modules.{t, a} X A)
    (U : X.ProEtᵒᵖ) (s : A.obj.obj U) (x : M.val.obj U) (y : N.val.obj U) :
    ScalarHomOrdinary.pure A M N U x (s • y) =
      s • ScalarHomOrdinary.pure A M N U x y := by
  unfold ScalarHomOrdinary.pure
  rw [TensorProduct.tmul_smul,
    (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
      (M.val ⊗ N.val)).app U).hom.map_smul]
  exact ((tensorObjIsoSheafification M N).inv.val.app U).hom.map_smul s _

private theorem balancedComponent_inv (α : R ⟶ S)
    (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (c : ScalarExtensionTensorCore.{t + 1, t, max a (t + 1)}
      (J := Scheme.ProEt.topology X) R S α)
    (A : Modules.{t, a} X R) (D : Modules.{t, a} X S)
    (b : changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α A ≅ D) (M : Modules.{t, a} X R)
    (U : X.ProEtᵒᵖ) (s q : S.obj.obj U) (x : M.val.obj U) (y : A.val.obj U) :
    (balancedComponent α p c A D b M).inv.val.app U
      (ScalarHomOrdinary.pure S (p.ordinary.obj M) D U (scalar p M U s x)
        (b.hom.val.app U (scalarExtensionSection α A U q y))) =
      scalar p ((monoidalCategory R).tensorObj M A) U (s * q)
        (ScalarHomOrdinary.pure R M A U x y) := by
  have hs (H : Modules.{t, a} X R) (v : H.val.obj U) (z : S.obj.obj U) :
      scalar p H U z v = z • scalar p H U 1 v := by
    change SuccessiveDerivedQuotient.sectionTensor p H U z v =
      z • SuccessiveDerivedQuotient.sectionTensor p H U 1 v
    exact SuccessiveDerivedQuotient.sectionTensor_smul_one p H U z v
  have hq : scalarExtensionSection α A U q y =
      q • scalarExtensionSection α A U 1 y := by
    simpa only [mul_one] using (scalarExtensionSection_smul α A U q 1 y).symm
  have hf := balancedComponent_hom α p c A D b M U 1 x y
  have hgen : ScalarHomOrdinary.pure S (p.ordinary.obj M) D U
      (scalar p M U s x) (b.hom.val.app U (scalarExtensionSection α A U q y)) =
      (s * q) • ScalarHomOrdinary.pure S (p.ordinary.obj M) D U
        (scalar p M U 1 x) (b.hom.val.app U (scalarExtensionSection α A U 1 y)) := by
    rw [hq, (b.hom.val.app U).hom.map_smul, pure_smul_second, hs M x s]
    rw [pure_smul_first, smul_smul, mul_comm q s]
  rw [hgen, ← hf, ← (balancedComponent α p c A D b M).hom.val.app U |>.hom.map_smul,
    ← hs]
  exact congrArg (fun f ↦ f.val.app U
    (scalar p ((monoidalCategory R).tensorObj M A) U (s * q)
      (ScalarHomOrdinary.pure R M A U x y)))
    (balancedComponent α p c A D b M).hom_inv_id

private theorem balancedComponent_natural (α : R ⟶ S)
    (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (c : ScalarExtensionTensorCore.{t + 1, t, max a (t + 1)}
      (J := Scheme.ProEt.topology X) R S α)
    (A : Modules.{t, a} X R) (D : Modules.{t, a} X S)
    (b : changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α A ≅ D)
    {M M' : Modules.{t, a} X R} (f : M ⟶ M') :
    p.ordinary.map ((tensorRight A).map f) ≫ (balancedComponent α p c A D b M').hom =
      (balancedComponent α p c A D b M).hom ≫ (tensorRight D).map (p.ordinary.map f) := by
  obtain ⟨d⟩ := SuccessiveDerivedQuotient.adjData_exists p
  apply (d.ordinary.homEquiv _ _).injective
  apply ScalarHomOrdinary.pure_hom_ext R M A
  intro U x y
  have hu (H : Modules.{t, a} X R) (z : H.val.obj U) :
      (d.ordinary.unit.app H).val.app U z = scalar p H U 1 z := by
    rw [scalar_eq_sectionTensor α p H U 1 z]
    exact d.ordinary_unit H U z
  have hn (H H' : Modules.{t, a} X R) (g : H ⟶ H') (z : H.val.obj U) :
      (p.ordinary.map g).val.app U (scalar p H U 1 z) =
        scalar p H' U 1 (g.val.app U z) := by
    have h := congrArg (fun h ↦ h.val.app U z) (d.ordinary.unit.naturality g)
    change (d.ordinary.unit.app H').val.app U (g.val.app U z) =
      (p.ordinary.map g).val.app U ((d.ordinary.unit.app H).val.app U z) at h
    rw [hu, hu] at h
    exact h.symm
  simp only [Adjunction.homEquiv_unit]
  change (balancedComponent α p c A D b M').hom.val.app U
      ((p.ordinary.map ((tensorRight A).map f)).val.app U
        ((d.ordinary.unit.app _).val.app U (ScalarHomOrdinary.pure R M A U x y))) =
    ((tensorRight D).map (p.ordinary.map f)).val.app U
      ((balancedComponent α p c A D b M).hom.val.app U
        ((d.ordinary.unit.app _).val.app U (ScalarHomOrdinary.pure R M A U x y)))
  rw [hu, hu, hn]
  have hp (H : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)})
      (V : Modules.{t, a} X H) {N N' : Modules.{t, a} X H}
      (g : N ⟶ N') (z : N.val.obj U) (v : V.val.obj U) :
      ((tensorRight V).map g).val.app U (ScalarHomOrdinary.pure H N V U z v) =
        ScalarHomOrdinary.pure H N' V U (g.val.app U z) v := by
    change ((monoidalCategory H).whiskerRight g V).val.app U _ = _
    rw [← tensorHom_id g V]
    simpa only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] using
      ScalarHomOrdinary.pure_map H g (𝟙 V) U z v
  rw [hp]
  change (balancedComponent α p c A D b M').hom.val.app U
      (scalar p ((monoidalCategory R).tensorObj M' A) U 1
        (ScalarHomOrdinary.pure R M' A U (f.val.app U x) y)) =
    ((tensorRight D).map (p.ordinary.map f)).val.app U
      ((balancedComponent α p c A D b M).hom.val.app U
        (scalar p ((monoidalCategory R).tensorObj M A) U 1
          (ScalarHomOrdinary.pure R M A U x y)))
  rw [balancedComponent_hom α p c A D b M' U 1 (f.val.app U x) y,
    balancedComponent_hom α p c A D b M U 1 x y, hp, hn]

/-- The balanced ordinary comparison, before passage to complexes or localization.
Source: Stacks 07A4, proof of lemma-pullback-tensor-product; Modules on Sites 03EK.
(blueprint: lem-pur-ordinary-line-scalar-balanced-comparison).
Proof: scalar extension is strong monoidal by its sheafified balanced tensor maps.
Compose its binary tensor comparison with B_m on the second factor. The forward
map sends s tensor (x tensor y) to (s tensor x) tensor B_m(1 tensor y).
The inverse reassociates after B_m inverse and multiplies the two scalars.
Balancing moves alpha(r) between the two factors, so these formulas respect every
relation. Their composites fix pure tensors. The sheafification and tensor universal
properties prove the inverse identities and naturality. These operations are on
ordinary module sheaves; no derived comparison or evaluation square is asserted. -/
theorem ordinary_scalar_line_balanced
    (α : R ⟶ S) (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (L : Modules.{t, a} X R) (K : Modules.{t, a} X S)
    (B : ∀ m : ℤ, changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α (power.{t, a} L m) ≅ power.{t, a} K m)
    : ∃ o : ∀ m : ℤ, tensor.{t, a} L m ⋙ p.ordinary ≅
        p.ordinary ⋙ tensor.{t, a} K m,
      (∀ (m : ℤ) (M : Modules.{t, a} X R) (U : X.ProEtᵒᵖ)
        (x : M.val.obj U) (y : (power.{t, a} L m).val.obj U) (s : S.obj.obj U),
        ((o m).hom.app M).val.app U
          (scalar.{t, a, w} p ((tensor.{t, a} L m).obj M) U s
            (LineUnbounded.pureTensor.{t, a} X R M (power.{t, a} L m) U x y)) =
        LineUnbounded.pureTensor.{t, a} X S (p.ordinary.obj M) (power.{t, a} K m) U
          (scalar.{t, a, w} p M U s x)
          ((B m).hom.val.app U (scalarExtensionSection α (power.{t, a} L m) U 1 y))) ∧
      (∀ (m : ℤ) (M : Modules.{t, a} X R) (U : X.ProEtᵒᵖ)
        (x : M.val.obj U) (y : (power.{t, a} L m).val.obj U) (s q : S.obj.obj U),
        ((o m).inv.app M).val.app U
          (LineUnbounded.pureTensor.{t, a} X S (p.ordinary.obj M) (power.{t, a} K m) U
            (scalar.{t, a, w} p M U s x)
            ((B m).hom.val.app U (scalarExtensionSection α (power.{t, a} L m) U q y))) =
        scalar.{t, a, w} p ((tensor.{t, a} L m).obj M) U (s * q)
          (LineUnbounded.pureTensor.{t, a} X R M (power.{t, a} L m) U x y)) := by
  classical
  obtain ⟨c⟩ := exists_scalarExtensionTensorCore.{t + 1, t, max a (t + 1)}
    (J := Scheme.ProEt.topology X) R S α
  let o (m : ℤ) : tensor.{t, a} L m ⋙ p.ordinary ≅
      p.ordinary ⋙ tensor.{t, a} K m :=
    NatIso.ofComponents
      (balancedComponent α p c (power L m) (power K m) (B m))
      (fun f ↦ balancedComponent_natural α p c (power L m) (power K m) (B m) f)
  refine ⟨o, ?_, ?_⟩
  · intro m M U x y s
    change (balancedComponent α p c (power L m) (power K m) (B m) M).hom.val.app U
        (scalar p ((monoidalCategory R).tensorObj M (power L m)) U s
          (ScalarHomOrdinary.pure R M (power L m) U x y)) =
      ScalarHomOrdinary.pure S (p.ordinary.obj M) (power K m) U (scalar p M U s x)
        ((B m).hom.val.app U (scalarExtensionSection α (power L m) U 1 y))
    exact balancedComponent_hom α p c (power L m) (power K m) (B m) M U s x y
  · intro m M U x y s q
    change (balancedComponent α p c (power L m) (power K m) (B m) M).inv.val.app U
        (ScalarHomOrdinary.pure S (p.ordinary.obj M) (power K m) U (scalar p M U s x)
          ((B m).hom.val.app U (scalarExtensionSection α (power L m) U q y))) =
      scalar p ((monoidalCategory R).tensorObj M (power L m)) U (s * q)
        (ScalarHomOrdinary.pure R M (power L m) U x y)
    exact balancedComponent_inv α p c (power L m) (power K m) (B m) M U s q x y

end SheafOfModules.OrdinaryLineScalar
