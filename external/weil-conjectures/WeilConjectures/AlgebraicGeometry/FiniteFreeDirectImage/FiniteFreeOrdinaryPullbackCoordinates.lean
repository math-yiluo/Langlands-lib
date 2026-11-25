/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageBalancingComputed
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
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreePresentedScalarCoordinates
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeCoefficientPullback
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.Algebra.Homology.Finite.FiniteFreeScalarExtension

/-! # Ordinary finite-basis coordinates and scalar pullback

Source: Stacks Project, Tags 03EK and 03EL.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open SheafOfModules.SuccessiveDerivedQuotient
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

private theorem ordinaryBalancing_unit {Z W : Scheme.{u}} {q : Z ⟶ W}
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    {R S : Coefficients q} (a : CoefficientMap R S)
    (M : proEtaleRingModules W R.target) (V : W.ProEtᵒᵖ) (m : M.val.obj V) :
    ((ordinaryBalancing sW sZ a).hom.app M).val.app ((proEtaleBaseChange q).op.obj V)
      (((proEtaleRingModuleAdjunction q S.target S.source S.identification).unit.app
        ((sW.presentation a.target).ordinary.obj M)).val.app V
          (sectionTensor (sW.presentation a.target) M V 1 m)) =
    sectionTensor (sZ.presentation a.source)
      ((proEtaleRingModulePullback q R.target R.source R.identification).obj M)
      ((proEtaleBaseChange q).op.obj V) 1
      (((proEtaleRingModuleAdjunction q R.target R.source R.identification).unit.app M).val.app
        V m) := by
  let pW := sW.presentation a.target
  let pZ := sZ.presentation a.source
  let adjR := proEtaleRingModuleAdjunction q R.target R.source R.identification
  let adjS := proEtaleRingModuleAdjunction q S.target S.source S.identification
  let d := proEtaleRingRestrictionDirectImage q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm
  let χ := ordinaryBalancing sW sZ a
  have hu := unit_conjugateEquiv_symm
    ((sW.normalization.ordinaryAdjunction a.target).comp adjS)
    (adjR.comp (sZ.normalization.ordinaryAdjunction a.source)) d.hom M
  have he := congrArg (fun h ↦ h.val.app V m) hu
  change (d.hom.app ((pW.ordinary ⋙
      proEtaleRingModulePullback q S.target S.source S.identification).obj M)).val.app V
        ((adjS.unit.app (pW.ordinary.obj M)).val.app V
          (((sW.normalization.ordinaryAdjunction a.target).unit.app M).val.app V m)) =
    (χ.inv.app M).val.app ((proEtaleBaseChange q).op.obj V)
      (((sZ.normalization.ordinaryAdjunction a.source).unit.app
        ((proEtaleRingModulePullback q R.target R.source R.identification).obj M)).val.app
          ((proEtaleBaseChange q).op.obj V) ((adjR.unit.app M).val.app V m)) at he
  have hd (N : proEtaleRingModules Z S.source) (v : N.val.obj
      ((proEtaleBaseChange q).op.obj V)) :
      (d.hom.app N).val.app V v = v :=
    (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique q
      R.target S.target R.source S.source a.target a.source
      R.identification S.identification a.comm)).1 N V v
  rw [hd, sW.normalization.ordinary_unit, sZ.normalization.ordinary_unit] at he
  have hh := congrArg (fun x ↦ (χ.hom.app M).val.app
    ((proEtaleBaseChange q).op.obj V) x) he
  have hi := congrArg (fun h ↦ h.val.app ((proEtaleBaseChange q).op.obj V)
    (sectionTensor pZ ((proEtaleRingModulePullback q R.target R.source
      R.identification).obj M) ((proEtaleBaseChange q).op.obj V) 1
        ((adjR.unit.app M).val.app V m))) (χ.inv_hom_id_app M)
  exact hh.trans hi

private theorem ordinaryBalancing_pure_private {Z W : Scheme.{u}} {q : Z ⟶ W}
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    {R S : Coefficients q} (a : CoefficientMap R S)
    (M : proEtaleRingModules W R.target) (V : W.ProEtᵒᵖ)
    (b : S.target.obj.obj V) (m : M.val.obj V) :
    ((ordinaryBalancing sW sZ a).hom.app M).val.app ((proEtaleBaseChange q).op.obj V)
      (((proEtaleRingModuleAdjunction q S.target S.source S.identification).unit.app
        ((sW.presentation a.target).ordinary.obj M)).val.app V
          (sectionTensor (sW.presentation a.target) M V b m)) =
    sectionTensor (sZ.presentation a.source)
      ((proEtaleRingModulePullback q R.target R.source R.identification).obj M)
      ((proEtaleBaseChange q).op.obj V)
      ((proEtaleRingDirectImageMap q S.target S.source S.identification).hom.app V b)
      (((proEtaleRingModuleAdjunction q R.target R.source R.identification).unit.app M).val.app
        V m) := by
  erw [sectionTensor_smul_one (sW.presentation a.target) M V b m]
  erw [(((proEtaleRingModuleAdjunction q S.target S.source S.identification).unit.app
    ((sW.presentation a.target).ordinary.obj M)).val.app V).hom.map_smul]
  let VZ := (proEtaleBaseChange q).op.obj V
  let P := (proEtaleRingModulePullback q S.target S.source S.identification).obj
    ((sW.presentation a.target).ordinary.obj M)
  let b' : ((sheafCompose (ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.source).obj.obj VZ :=
    (proEtaleRingDirectImageMap q S.target S.source S.identification).hom.app V b
  let m' : P.val.obj VZ :=
    (((proEtaleRingModuleAdjunction q S.target S.source S.identification).unit.app
      ((sW.presentation a.target).ordinary.obj M)).val.app V
        (sectionTensor (sW.presentation a.target) M V 1 m))
  change ((ordinaryBalancing sW sZ a).hom.app M).val.app VZ (b' • m') = _
  erw [(((ordinaryBalancing sW sZ a).hom.app M).val.app
    ((proEtaleBaseChange q).op.obj V)).hom.map_smul, ordinaryBalancing_unit]
  exact (sectionTensor_smul_one (sZ.presentation a.source) _ _ _ _).symm

/-- Public export of the private `ordinaryBalancing_pure_private`
(used by `import all` importers; linter.privateModule). -/
alias ordinaryBalancing_pure := ordinaryBalancing_pure_private

private theorem presentedTensor_hom_ext_private (X : Scheme.{u}) (s : ScalarModel X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (θ : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅
      (proEtaleRingRestrictScalars a).obj (SheafOfModules.unit ((sheafCompose
        (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)))
    (M N : proEtaleRingModules X R)
    (f g : (proEtaleRingRestrictScalars a).obj ((s.presentation a).ordinary.obj M) ⟶ N)
    (h : ∀ (V : X.ProEtᵒᵖ) (b : S.obj.obj V) (m : M.val.obj V),
      f.val.app V (sectionTensor (s.presentation a) M V b m) =
        g.val.app V (sectionTensor (s.presentation a) M V b m)) : f = g := by
  let p := s.presentation a
  let U := proEtaleRingRestrictScalars a
  apply (cancel_epi (U.map (eqToHom (p.obj_eq M).symm))).mp
  apply SheafOfModules.scalarExtension_hom_ext_of_basis a d θ M N
  let VR := PresheafOfModules.toPresheaf ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj
  let VS := PresheafOfModules.toPresheaf ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj
  apply VR.map_injective
  change VS.map (SheafOfModules.tensorUnit a M) ≫
      VR.map (U.map (eqToHom (p.obj_eq M).symm) ≫ f).val =
    VS.map (SheafOfModules.tensorUnit a M) ≫
      VR.map (U.map (eqToHom (p.obj_eq M).symm) ≫ g).val
  dsimp only [VS]
  unfold SheafOfModules.tensorUnit
  simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  ext V z
  induction z using TensorProduct.inductionOn with
  | tmul b m => exact h V b m
  | add x y hx hy => simp_all

attribute [local instance] unitSMul_presentedScalarCoordinates

-- Elaborating the projected square expands both scalar and geometric adjunctions.
private theorem ordinaryCoordinate_square {Z W : Scheme.{u}} {q : Z ⟶ W}
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    (R S : Coefficients q) (a : CoefficientMap R S) (d : ℕ)
    (θ : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)) ≅
      (proEtaleRingRestrictScalars a.target).obj (SheafOfModules.unit ((sheafCompose
        (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)))
    (θZ : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose (ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.source)) ≅
      (proEtaleRingRestrictScalars a.source).obj (SheafOfModules.unit ((sheafCompose
        (ProEt.topology Z) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.source)))
    (hcoord : ∀ (V : W.ProEtᵒᵖ) (b : S.target.obj.obj V) (i : Fin d),
      (θZ.inv ≫ Pi.π _ i).val.app ((proEtaleBaseChange q).op.obj V)
        ((proEtaleRingDirectImageMap q S.target S.source S.identification).hom.app V b) =
      (proEtaleRingDirectImageMap q R.target R.source R.identification).hom.app V
        ((θ.inv ≫ Pi.π _ i).val.app V b))
    (φW : (sW.presentation a.target).ordinary ⋙ proEtaleRingRestrictScalars a.target ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    (φZ : (sZ.presentation a.source).ordinary ⋙ proEtaleRingRestrictScalars a.source ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    (hW : ∀ (M : proEtaleRingModules W R.target) (V : W.ProEtᵒᵖ)
      (b : S.target.obj.obj V) (m : M.val.obj V) (i : Fin d),
      (φW.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) i).val.app V
        (sectionTensor (sW.presentation a.target) M V b m) =
      (θ.inv ≫ Pi.π _ i).val.app V b • m)
    (hZ : ∀ (M : proEtaleRingModules Z R.source) (V : Z.ProEtᵒᵖ)
      (b : S.source.obj.obj V) (m : M.val.obj V) (i : Fin d),
      (φZ.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) i).val.app V
        (sectionTensor (sZ.presentation a.source) M V b m) =
      (θZ.inv ≫ Pi.π _ i).val.app V b • m)
    (M : proEtaleRingModules W R.target) :
    (proEtaleRingModulePullback q R.target R.source R.identification).map (φW.hom.app M) ≫
      (PreservesProduct.iso (proEtaleRingModulePullback q R.target R.source R.identification)
        (fun _ : Fin d ↦ M)).hom =
    (proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm).app
        ((sW.presentation a.target).ordinary.obj M) ≫
      (proEtaleRingRestrictScalars a.source).map ((ordinaryBalancing sW sZ a).hom.app M) ≫
      φZ.hom.app ((proEtaleRingModulePullback q R.target R.source R.identification).obj M) := by
  let F := proEtaleRingModulePullback q R.target R.source R.identification
  let adj := proEtaleRingModuleAdjunction q R.target R.source R.identification
  apply limit.hom_ext
  rintro ⟨i⟩
  change (F.map (φW.hom.app M) ≫ (PreservesProduct.iso F (fun _ : Fin d ↦ M)).hom) ≫
      Pi.π (fun _ : Fin d ↦ F.obj M) i = _
  rw [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π, ← F.map_comp]
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  erw [← adj.unit.naturality (φW.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) i)]
  apply presentedTensor_hom_ext_private W sW a.target d θ
  intro V b m
  change ((adj.unit.app M).val.app V)
      ((φW.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) i).val.app V
        (sectionTensor (sW.presentation a.target) M V b m)) =
    (φZ.hom.app (F.obj M) ≫ Pi.π (fun _ : Fin d ↦ F.obj M) i).val.app
      ((proEtaleBaseChange q).op.obj V)
      (((ordinaryBalancing sW sZ a).hom.app M).val.app ((proEtaleBaseChange q).op.obj V)
        (((proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
          a.target a.source R.identification S.identification a.comm).app
            ((sW.presentation a.target).ordinary.obj M)).val.app
              ((proEtaleBaseChange q).op.obj V)
                ((adj.unit.app _).val.app V
                  (sectionTensor (sW.presentation a.target) M V b m))))
  erw [hW M V b m i]
  erw [((adj.unit.app M).val.app V).hom.map_smul]
  erw [restrictionPullback_unit R S a ((sW.presentation a.target).ordinary.obj M) V
    (sectionTensor (sW.presentation a.target) M V b m)]
  erw [ordinaryBalancing_pure_private sW sZ a M V b m]
  erw [hZ (F.obj M) ((proEtaleBaseChange q).op.obj V)
    ((proEtaleRingDirectImageMap q S.target S.source S.identification).hom.app V b)
    ((adj.unit.app M).val.app V m) i, hcoord V b i]
  rfl

/-- A basis and its pullback give ordinary coordinate isomorphisms whose square
commutes with the actual geometric and scalar comparisons.
Source: Stacks Project, Tags 03EK, 03EL and 06YY.
(blueprint: lem-sp-finite-free-ordinary-pullback-coordinates).

Proof: transport the regular-module basis along exact inverse image and the regular
module unit comparison. The tensor coordinates of these bases are natural. They
make extension finite powers, and hence both universal derived counits invertible.
Project the ordinary square to one coordinate and transpose through the geometric
adjunction. On a local pure tensor its two sides are the pulled-back coordinate of
the coefficient multiplied by the pulled-back module section. Naturality of the
geometric unit identifies the coefficient coordinates, and conjugation identifies
the ordinary balancing on pure tensors. Tensor generation and product
extensionality finish the square. The argument includes the empty basis. -/
theorem finiteFreeDirectImage_ordinaryPullbackCoordinates {Z W : Scheme.{u}} (q : Z ⟶ W)
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    (R S : Coefficients q) (a : CoefficientMap R S) (d : ℕ)
    (hfree : Nonempty ((proEtaleRingRestrictScalars a.target).obj
      (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)) ≅
      SheafOfModules.free (R := (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)
        (ULift.{u + 1} (Fin d)))) :
    ∃ (φW : (sW.presentation a.target).ordinary ⋙ proEtaleRingRestrictScalars a.target ≅
        Functor.const (Discrete (Fin d)) ⋙ lim)
      (φZ : (sZ.presentation a.source).ordinary ⋙ proEtaleRingRestrictScalars a.source ≅
        Functor.const (Discrete (Fin d)) ⋙ lim),
      (∀ H : HomotopyCategory (proEtaleRingModules W R.target) (.up ℤ),
        IsIso ((sW.presentation a.target).counit.app H)) ∧
      (∀ H : HomotopyCategory (proEtaleRingModules Z R.source) (.up ℤ),
        IsIso ((sZ.presentation a.source).counit.app H)) ∧
      ∀ M : proEtaleRingModules W R.target,
        (proEtaleRingModulePullback q R.target R.source R.identification).map (φW.hom.app M) ≫
          (PreservesProduct.iso
            (proEtaleRingModulePullback q R.target R.source R.identification)
            (fun _ : Fin d ↦ M)).hom =
        (proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
          a.target a.source R.identification S.identification a.comm).app
            ((sW.presentation a.target).ordinary.obj M) ≫
          (proEtaleRingRestrictScalars a.source).map
            ((ordinaryBalancing sW sZ a).hom.app M) ≫
          φZ.hom.app ((proEtaleRingModulePullback q R.target R.source R.identification).obj M) := by
  let θ := basisPowerIso W R.target d ≪≫ hfree.some.symm
  obtain ⟨θZ, hcoord⟩ := finiteFreeDirectImage_coefficientPullback R S a d θ
  obtain ⟨φW, _, _, hεW, hW⟩ :=
    finiteFreeDirectImage_presentedScalarCoordinates W sW a.target d θ
  obtain ⟨φZ, _, _, hεZ, hZ⟩ := finiteFreeDirectImage_presentedScalarCoordinates Z sZ a.source d
    θZ
  exact ⟨φW, φZ, hεW, hεZ, ordinaryCoordinate_square sW sZ R S a d θ θZ hcoord φW φZ hW hZ⟩

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage

namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage
/-- Public export of the private `presentedTensor_hom_ext_private` (used by `import all` importers;
linter.privateModule). -/
alias presentedTensor_hom_ext := presentedTensor_hom_ext_private

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
