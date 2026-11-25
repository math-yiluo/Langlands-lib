/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Homology.InternalHom
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
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
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.WeilSheaf.DerivedHom
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSite
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
public import WeilConjectures.CategoryTheory.RingedForgetTwoInjective.RingedForgetTwoInjectiveModels
import WeilConjectures.CategoryTheory.Ringed.Sheaf.RingedSheafHomComplexComparison
import WeilConjectures.CategoryTheory.Ringed.Sheaf.RingedSheafHomComparisonDescent
import WeilConjectures.CategoryTheory.Ringed.RingedHomComplexComparison
import WeilConjectures.CategoryTheory.K.KInjectiveHomComparisonDescent
import WeilConjectures.WeilSheaf.Native.NativeStandardHomRepresentatives
import WeilConjectures.WeilSheaf.SixFunctors.UnderlyingStandardHomRepresentatives

/-! # Two K-injective models and forgetting the ringed action

Source: Stacks Project, Tags 0A95 and 08J7; the internal-Hom paragraph of
blueprint/sec-six-functors/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md;
the native signed model in WeilConjectures.WeilSheaf.DerivedHom
(blueprint: lem-sf-ringed-forget-two-injective-hom).

The comparison data specify product projections, not global Hom groups. The native
normalization retains the row sign of bifunctorHomObj and its degree/source-index correction.
-/

@[expose] public noncomputable section

set_option genSizeOfSpec false
set_option genInjectivity false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe b vb wb a va wa c v r d vd s u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolutionIso

namespace CategoryTheory.RingedForgetTwoInjective

section Forgetting

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [∀ A : Type (max c v r), PreservesLimitsOfShape (Discrete A) U]
  [U.PreservesKInjectiveComplexes]
  (h : Functor.uncurry.obj (SheafOfModules.homFunctor (R := R)) ⋙ U ≅
    (U.op.prod U) ⋙ Functor.uncurry.obj (SheafOfModules.homFunctor (R := R')))

end Forgetting
end CategoryTheory.RingedForgetTwoInjective

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open CategoryTheory.RingedForgetTwoInjective

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The twisted-action-site two-injective model is canonically the native model after its
explicit sign normalization, and commutes with forgetting the Frobenius structure.
Source: Stacks 0A95 and 08J7; native DerivedHom.lean and BifunctorHomComplex.lean
(blueprint: lem-sf-ringed-forget-two-injective-hom).
Proof:
1. Locally finite span and locally finite-subextension values agree: finitely many spanning
values generate a finite intermediate field by algebraicity. Conversely the span of values
in a finite intermediate field is finite dimensional. This argument is local on every test
space, without a compactness assumption.
2. Apply standardHomModel to the native and underlying Hom bifunctors. It retains the actual
native complex and rescales the degree-n, source-p projection by (-1)^(np). Its proved product,
differential and map equations give StandardModel. The identity chain map then has the
required sign_projection, and its naturality is immediate.
3. Use nativeStandardHomRepresentatives and underlyingStandardHomRepresentatives for the two
derived extensions and their natural arbitrary-source/K-injective-target representative maps.
The former also supplies the slice comparison with derivedHom, normalized by the actual
bifunctorRHomOfComplexObjIso. Since the sign map is the identity, this is native_normalization.
4. The actual forgetting functor preserves products and K-injectives by forgetKInjective.
Its internal-Hom comparison is the identity on the underlying modules. Apply
ringedHomComplexComparison using both standard models to obtain the chain comparison with
its specified projection formula. Apply kInjectiveHomComparisonDescent to this comparison
and the two representative systems. Its representative equation includes both localization
factor legs and is exactly the final required compatibility. Assemble all fields. -/
theorem native_two_injective_hom_model
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (TwoInjectiveHomModel (k₀ := k₀) (l := l) (X := X)) := by
  let S := standardHomModel (ihomBifunctor k₀ l X)
  let T := standardHomModel (underlyingHomBifunctor (k₀ := k₀) (l := l) (X := X))
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  have : U.PreservesKInjectiveComplexes := forgetKInjective
  have : HasLimitsOfShape (Discrete ℤ)
      (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) := inferInstance
  have : PreservesLimitsOfShape (Discrete ℤ) U := by
    let A := ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
    have : HasColimitsOfSize.{u + 1, u + 1} A := inferInstance
    have : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} A
    exact
      (Endofunctor.IsoAlgebra.Free.adjunction
        (WeilSheaf.frobeniusPullback k₀ l X)).rightAdjoint_preservesLimits
        |>.preservesLimitsOfShape
  let h : Functor.uncurry.obj (ihomBifunctor k₀ l X) ⋙ U ≅
      (U.op.prod U) ⋙ Functor.uncurry.obj
        (underlyingHomBifunctor (k₀ := k₀) (l := l) (X := X)) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro P Q f
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl)
  obtain ⟨H, ρ, e, he⟩ := nativeStandardHomRepresentatives
    (k₀ := k₀) (l := l) (X := X)
  obtain ⟨H', ⟨ρ'⟩⟩ := underlyingStandardHomRepresentatives
    (k₀ := k₀) (l := l) (X := X)
  obtain ⟨chain, hc⟩ := ringedHomComplexComparison U
    (ihomBifunctor k₀ l X) (underlyingHomBifunctor (k₀ := k₀) (l := l) (X := X))
    S.complex T.complex S.π T.π S.product T.product
    S.differential T.differential S.map_projection T.map_projection h
  obtain ⟨derived, hd⟩ := kInjectiveHomComparisonDescent U S.complex T.complex H H'
    ρ.iso ρ'.iso ρ.naturality ρ'.naturality chain
  refine ⟨{
    coefficients := ?_
    source := S
    target := T
    sign := fun _ _ ↦ Iso.refl _
    sign_projection := ?_
    sign_naturality := ?_
    hom := H
    representatives := ρ
    underlyingHom := H'
    underlyingRepresentatives := ρ'
    native := e
    native_normalization := ?_
    chain := chain
    chain_projection := hc
    derived := derived
    derived_representative := hd }⟩
  · intro A _ f
    rw [PadicAlgCl.mem_locallyFiniteFunctions_iff]
    constructor
    · intro hf x
      obtain ⟨N, hN, hfin⟩ := hf x
      obtain ⟨F, hF⟩ := Module.Finite.iff_fg.mp hfin
      let E := IntermediateField.adjoin ℚ_[l] (F : Set (PadicAlgCl l))
      have : FiniteDimensional ℚ_[l] E :=
        IntermediateField.finiteDimensional_adjoin
          (fun a _ ↦ Algebra.IsIntegral.isIntegral a)
      refine ⟨N, hN, ⟨E, inferInstance⟩, ?_⟩
      intro y hy
      have hm : f y ∈ Submodule.span ℚ_[l] (f '' N) :=
        Submodule.subset_span ⟨y, hy, rfl⟩
      rw [← hF] at hm
      exact (Submodule.span_le.mpr (IntermediateField.subset_adjoin ℚ_[l] _) :
        Submodule.span ℚ_[l] (F : Set (PadicAlgCl l)) ≤ E.toSubalgebra.toSubmodule) hm
    · intro hf x
      obtain ⟨N, hN, E, hE⟩ := hf x
      have : FiniteDimensional ℚ_[l] E.val.toSubalgebra.toSubmodule := E.property
      refine ⟨N, hN, Submodule.finiteDimensional_of_le
        (S₂ := E.val.toSubalgebra.toSubmodule) (Submodule.span_le.mpr ?_)⟩
      rintro a ⟨y, hy, rfl⟩
      exact hE y hy
  · intro K I n p q hpq
    exact Category.id_comp _
  · intro K K' I I' f g
    dsimp only [S, standardHomModel, nativeHomComplex, Iso.refl_hom]
    simp only [Category.comp_id, Category.id_comp, Quiver.Hom.unop_op]
  · intro L K _
    change (e L).hom.app (op (DerivedCategory.Q.obj K)) ≫
      (DerivedCategory.bifunctorRHomOfComplexObjIso (ihomBifunctor k₀ l X)
        (DerivedCategory.kInjectiveRep L) K).hom ≫ DerivedCategory.Q.map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact he L K

end AlgebraicGeometry.ProEtaleWeilSheaf
