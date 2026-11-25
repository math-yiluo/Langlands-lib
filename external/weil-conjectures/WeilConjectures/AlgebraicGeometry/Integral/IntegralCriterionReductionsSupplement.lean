/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import Mathlib.Topology.Category.Profinite.AsLimit
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import all WeilConjectures.SixFunctors.ProEtale.IntegralCompletionPresentationSupplement
import WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedSectionSquares
import WeilConjectures.SixFunctors.ProEtale.InternalRoosCompleteness
import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import Mathlib.Topology.Algebra.Order.Field
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.SuccessiveQuotientFlatTensorSequence
import all WeilConjectures.SixFunctors.Supporting.StrictDvrFlatTensorSequence
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCoefficientRegularQuotients
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteScalarRestrictionConstructible
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions

/-!
# Constructibility of all integral reductions from the first
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint

private theorem finiteConstantEndomorphism (X : Scheme.{u})
    (h : sfbFiniteConstantSets X ⟶ sfbFiniteConstantSets X) : h = 𝟙 _ := by
  let J := Scheme.ProEt.topology X
  let O := FintypeCat.of (ULift.{u} Unit)
  let F := sfbFiniteConstantSets X
  have ht : IsTerminal (ULift.{u + 1, u} (ULift.{u} Unit)) :=
    (Types.isTerminalEquivUnique _).symm inferInstance
  have ht' : IsTerminal (F.obj O) :=
    (ht.isTerminalObj (constantSheaf J (Type (u + 1))) _).isTerminalObj
      (sheafToPresheaf J (Type (u + 1))) _
  have hO : h.app O = 𝟙 _ := ht'.hom_ext _ _
  apply NatTrans.ext
  funext T
  apply sheafify_hom_ext J _ _
    (((constantSheaf J (Type (u + 1))).obj (ULift.{u + 1, u} T)).property)
  ext V x
  let k : O ⟶ T := FintypeCat.homMk fun _ ↦ x.down
  let z := (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
    (ULift.{u + 1, u} (ULift.{u} Unit)))).app V (ULift.up (ULift.up ()))
  have hn := congrArg (fun t ↦ t.app V) (h.naturality k)
  rw [hO, Category.id_comp] at hn
  have hc : (F.map k).app V z =
      (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1, u} T))).app V x := by
    exact (congrArg (fun t ↦ t.app V
      (ULift.up (ULift.up () : ULift.{u} Unit))) (toSheafify_naturality J
      ((Functor.const X.ProEtᵒᵖ).map
        (uliftFunctor.{u + 1, u}.map ((forget FintypeCat).map k))))).symm
  change (h.app T).app V
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1, u} T))).app V x) =
    (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1, u} T))).app V x
  rw [← hc]
  exact congrArg (fun t ↦ t z) hn

private theorem finiteRepresentation_unique (X : Scheme.{u})
    (a b : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X) : a = b := by
  apply Iso.ext
  have h := finiteConstantEndomorphism X (a.hom ≫ b.inv)
  have h' := congrArg (fun f ↦ f ≫ b.hom) h
  simpa using h'

private theorem continuousRingSheaf_topology_eq (T : Type u) [Ring T]
    (t₁ t₂ : TopologicalSpace T) (h : t₁ = t₂)
    (h₁ : @IsTopologicalRing T t₁ _) (h₂ : @IsTopologicalRing T t₂ _) :
    @Profinite.continuousMapRingSheafOfUniverse.{u, u} T t₁ _ h₁ =
      @Profinite.continuousMapRingSheafOfUniverse.{u, u} T t₂ _ h₂ := by
  subst t₂
  rfl

private theorem integralPointMon_eq (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Mon.mk (DerivedNakayama.integerRing l E) = sfbCondensedIntegers l E := by
  have hm : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  have ht := congrArg (fun m : PseudoMetricSpace E ↦
    m.toUniformSpace.toTopologicalSpace) hm.symm
  have hti := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  have hs := continuousRingSheaf_topology_eq
    (Padic.coefficientExtensionIntegers l E) _ _ hti
    (by let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField; infer_instance)
    (by let := spectralNorm.normedField (Padic l) E; infer_instance)
  let F : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} →
      Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := fun R ↦
    Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)
  exact congrArg F hs

attribute [local instance] Sheaf.monoidalCategory in
private theorem ringPresheafMon_eq
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (R : Sheaf J RingCat.{u + 1}) :
    (sheafToPresheaf J Ab.{u + 1}).monObjObj
      ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R) =
        R.obj.monObjCompForget₂ := by
  apply MonObj.ext
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  let : MonObj A.obj := R.obj.monObjCompForget₂
  exact Sheaf.μ_comp_map_mul A

private theorem liftSectionRingIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (A : Sheaf J Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (S : Sheaf J CommRingCat.{u + 1})
    (a : A ≅ (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    [IsMonHom a.hom] :
    ∃! e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A ≅ S,
      (sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map e.hom = a.hom := by
  let F := (Monoidal.monFunctorCategoryEquivalence Cᵒᵖ Ab.{u + 1}).functor
  let h := Functor.whiskerRight
    (F.map ((sheafToPresheaf J Ab.{u + 1}).mapMon.map (Mon.ofHom a.hom)))
    InternalAbelianSheafModule.monToRing
  let k := Functor.whiskerRight
    (F.map ((sheafToPresheaf J Ab.{u + 1}).mapMon.map (Mon.ofHom a.inv)))
    InternalAbelianSheafModule.monToRing
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let B := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hmon : (sheafToPresheaf J Ab.{u + 1}).monObjObj B = R.obj.monObjCompForget₂ :=
    ringPresheafMon_eq J R
  let BP := F.obj ((sheafToPresheaf J Ab.{u + 1}).mapMon.obj (Mon.mk B)) ⋙
    InternalAbelianSheafModule.monToRing
  let b : BP ≅ R.obj := by
    refine NatIso.ofComponents (fun U ↦ ?_) (fun _ ↦ ?_)
    · refine @RingEquiv.toRingCatIso (BP.obj U) (R.obj.obj U)
        (RingCat.ring _) (RingCat.ring _) ?_
      refine { toEquiv := Equiv.refl _, map_add' := fun _ _ ↦ rfl, map_mul' := ?_ }
      intro x y
      change (((sheafToPresheaf J Ab.{u + 1}).monObjObj B).mul.app U).hom
        (TensorProduct.tmul ℤ x y) = _
      have hh := congrArg (fun m : MonObj B.obj ↦ m.mul) hmon
      rw [hh]
      rfl
    · ext x
      rfl
  let d : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A ≅ S :=
    { hom := ⟨{ app := fun U ↦
                  @CommRingCat.ofHom
                    ((InternalAbelianSheafModule.sectionRingSheaf J A).obj.obj U)
                    (S.obj.obj U) _ _ ((h ≫ b.hom).app U).hom
                naturality := fun U V f ↦ by
                  apply (forget₂ CommRingCat RingCat).map_injective
                  exact (h ≫ b.hom).naturality f }⟩
      inv := ⟨{ app := fun U ↦
                  @CommRingCat.ofHom (S.obj.obj U)
                    ((InternalAbelianSheafModule.sectionRingSheaf J A).obj.obj U)
                    _ _ ((b.inv ≫ k).app U).hom
                naturality := fun U V f ↦ by
                  apply (forget₂ CommRingCat RingCat).map_injective
                  exact (b.inv ≫ k).naturality f }⟩
      hom_inv_id := by
        ext U x
        have hh := congr_app (congrArg (fun f : A ⟶ A ↦ f.hom) a.hom_inv_id) U
        exact ConcreteCategory.congr_hom hh x
      inv_hom_id := by
        ext U x
        have hh := congr_app (congrArg (fun f : B ⟶ B ↦ f.hom) a.inv_hom_id) U
        exact ConcreteCategory.congr_hom hh x }
  have hd : (sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map d.hom = a.hom := by
    ext U x
    rfl
  refine ⟨d, hd, ?_⟩
  intro e he
  apply Iso.ext
  apply (sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).map_injective
  exact he.trans hd.symm

private noncomputable def restrictionRoundTrip
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.restrictScalars.{u + 1} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{u + 1} S) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (c.inv.hom.app U).hom
        (c.hom.hom.app U).hom (RingHom.id _) (by
          have h := congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U
          exact (congrArg RingCat.Hom.hom h).symm) (M.val.obj U)).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj U))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)

private theorem restrictionTriangle
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) (M : SheafOfModules.{u + 1} S) :
    (SheafOfModules.restrictScalars c.hom).map ((restrictionRoundTrip c).inv.app M) ≫
      (restrictionRoundTrip c.symm).hom.app
        ((SheafOfModules.restrictScalars c.hom).obj M) = 𝟙 _ := by
  ext U x
  rfl

private noncomputable def restrictionEquivalence
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (restrictionRoundTrip c).symm
  counitIso := restrictionRoundTrip c.symm
  functor_unitIso_comp := restrictionTriangle c

private theorem restriction_isEquivalence
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} c.hom).IsEquivalence :=
  (restrictionEquivalence c).isEquivalence_functor

private def integralEncoding (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) : IntegralPresentation.Encoding l E X where
  ringIso := integralSectionRingIso l E X
  modules := (integralSectionFunctor l E X).asEquivalence
  functor_eq := rfl
  additive := by
    change (integralSectionFunctor l E X).Additive
    infer_instance
  inverseAdditive := by
    let : (integralSectionFunctor l E X).asEquivalence.functor.Additive :=
      inferInstanceAs (integralSectionFunctor l E X).Additive
    infer_instance

private theorem finiteTopology_discrete (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have hm : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  have ht := congrArg (fun m : PseudoMetricSpace E ↦
    m.toUniformSpace.toTopologicalSpace) hm
  have hti := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  apply QuotientAddGroup.discreteTopology
  apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
  have hb := (Padic.coefficientExtension_integers_coset_basis l E 0).mem_of_mem
    (i := n) trivial
  change @Membership.mem (Set (Padic.coefficientExtensionIntegers l E)) _ _
    (@nhds _ (TopologicalSpace.induced _ _) 0) _ at hb
  change @Membership.mem (Set (Padic.coefficientExtensionIntegers l E)) _ _
    (@nhds _ (TopologicalSpace.induced _ _) 0) _
  rw [← hti]
  have he : {y : Padic.coefficientExtensionIntegers l E |
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) y =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) 0} =
      (Padic.coefficientExtensionIdeal l E (n + 1)).toAddSubgroup := by
    ext y
    change _ = _ ↔ y ∈ Padic.coefficientExtensionIdeal l E (n + 1)
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
  rw [he] at hb
  exact hb

private theorem finiteEncoding_ringIso_unique
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) (e f : FiniteDiscreteOrdinary.Encoding A X) :
    e.ringIso = f.ringIso := by
  let : HasWeakSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
    (WeilConjectures.integralCoefficientRingSheafify.{u, u} X).isRightAdjoint
  apply Iso.ext
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _
    (FiniteDiscreteOrdinary.sectionRing A X).property
  ext U a
  exact (e.normalization U a).trans (f.normalization U a).symm

private theorem finiteEncoding_functor_eq
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) (e f : FiniteDiscreteOrdinary.Encoding A X) :
    e.ordinary.functor = f.ordinary.functor := by
  rw [e.ordinary_functor, f.ordinary_functor, finiteEncoding_ringIso_unique A X e f]

private theorem finiteBounded_iso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Finite A]
    (X : Scheme.{u}) {K L : Scheme.proEtaleDerivedCategory X A} (e : K ≅ L) :
    FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X K ↔
      FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X L := by
  constructor
  · intro h
    exact ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e h.1,
      fun q ↦ FiniteDiscreteOrdinary.constructible_of_iso A X
        ((DerivedCategory.homologyFunctor _ q).mapIso e) (h.2 q)⟩
  · intro h
    exact ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e.symm h.1,
      fun q ↦ FiniteDiscreteOrdinary.constructible_of_iso A X
        ((DerivedCategory.homologyFunctor _ q).mapIso e.symm) (h.2 q)⟩

private theorem finiteEncoding_constructible
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A] (X : Scheme.{u}) [IsNoetherian X]
    (e : FiniteDiscreteOrdinary.Encoding A X)
    (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A X)) :
    constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X K ↔
      FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X
        (e.ordinaryDerived.functor.obj K) := by
  obtain ⟨f, hf⟩ := FiniteDiscreteOrdinary.finiteCoefficientModelComparison A X
  have h := finiteEncoding_functor_eq A X e f
  exact (hf.boundedConstructible K).trans
    (finiteBounded_iso A X
      ((Functor.mapDerivedCategoryNatIso (eqToIso h)).app K).symm)

attribute [local irreducible] WeilConjectures.scalarReductionExistence
  WeilConjectures.scalarReductionDerivedExistence

private theorem reductionAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

private theorem reductionAbLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective Ab.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

private theorem reductionRingSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  hasSheafifyEssentiallySmallSite _ _

private theorem reductionSiteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance] reductionSiteSmall

attribute [local instance] reductionAbSheafify reductionAbLocallyBijective

attribute [local instance] WeilConjectures.scalarReductionExtensionAdditive
  WeilConjectures.scalarReductionRestrictionLimits
  WeilConjectures.scalarReductionRestrictionColimits
  Scheme.proEtaleRingRestrictScalars_preservesFiniteLimits
  Scheme.proEtaleRingRestrictScalars_preservesFiniteColimits

private def tensorCoefficientIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective Ab.{u + 1}] [HasSheafify J Ab.{u + 1}]
    {B : Sheaf J CommRingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)} (e : M ≅ N) :
    SheafOfModules.leftTensorSheaf M ≅ SheafOfModules.leftTensorSheaf N :=
  NatIso.ofComponents (fun P ↦ (SheafOfModules.siteSheafTensorRight P).mapIso e)
    (fun f ↦ (SheafOfModules.siteSheafTensorSecondMap_naturality e.hom f).symm)

end AlgebraicGeometry.ProEtale
