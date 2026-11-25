/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Locally.LocallyFiniteCoefficientRingRealization
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarRestrictionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero

/-! # Native modules, scalar local models, and bounded constructibility

The ordinary category is the existing sectionwise module category of the reconstructed
ring sheaf of R_T. Its existing internal-module equivalence fixes that reconstruction.
The comparison to native modules is normalized by the canonical coefficient realization.
- May be used on arbitrary covering members, which need not be finite type.
- Constructibility is compared on separated finite-type schemes over the given field.
- Both derived categories are ordinary localizations at quasi-isomorphisms.

## References

* Stacks 03CW, 03CY, 03EK and 05RU
* Stacks 03CW, ordinary presentation in the module comparison
* Stacks 05RU and the size convention in the module comparison
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj IntermediateField

namespace AlgebraicGeometry.ProEtale

/-- The normalized coefficient realization, chosen from its already recorded theorem.
Its finite-field normalization uniquely determines the underlying ring isomorphism. -/
abbrev nativeModuleCoefficientIso (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u}) :=
  (locallyFiniteCoefficientRing_realization ℓ).choose T

/-- The chosen realization is a ring morphism, by the existing realization theorem. -/
instance nativeModuleCoefficientIso_isMonHom (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u}) :
    IsMonHom (nativeModuleCoefficientIso ℓ T).hom :=
  (locallyFiniteCoefficientRing_realization ℓ).choose_spec.1 T

/-- The existing equivalence with sectionwise R_T-modules; no new module category is made. -/
abbrev nativeOrdinaryPresentation (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T)
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T)

/-- Ordinary, sectionwise module sheaves over R_T, using its reconstructed ring sheaf. -/
abbrev NativeOrdinaryModules (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u}) :=
  ringedSiteModules.{u + 1, u + 1, u, u + 1} ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T)
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T)))

/-- The ordinary derived localization in the larger chosen universe. -/
instance nativeOrdinaryModules_hasDerivedCategory (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) : HasDerivedCategory.{u + 2} (NativeOrdinaryModules ℓ T) :=
  HasDerivedCategory.standard _

/-- Forget scalar linearity, transport the action along theta, and read it on sections.
Thus r acts by theta(r), with the original abelian sheaf and restriction maps. -/
abbrev nativeToOrdinaryModules (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u}) :
    AdicSheaf ℓ T ⥤ NativeOrdinaryModules ℓ T :=
  AdicSheaf.forgetAb ℓ T ⋙ Mod.comap (nativeModuleCoefficientIso ℓ T).hom ⋙
    (nativeOrdinaryPresentation ℓ T).functor

/-- Restriction in the ordinary presentation is the existing coefficient-module pullback. -/
abbrev ordinaryModuleRestriction (ℓ : ℕ) [Fact ℓ.Prime]
    {S T : Scheme.{u}} (h : S ⟶ T) :
    NativeOrdinaryModules ℓ T ⥤ NativeOrdinaryModules ℓ S :=
  (nativeOrdinaryPresentation ℓ T).inverse ⋙
    CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) h ⋙
      (nativeOrdinaryPresentation ℓ S).functor

/-- The finite scalar model, expressed in the ordinary sectionwise presentation. -/
abbrev ordinaryScalarModel (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u})
    (P : Mod Ab.{u + 1} (scalarRingObj (Profinite.padicAlgClRingObj ℓ))) :
    NativeOrdinaryModules ℓ T :=
  (nativeOrdinaryPresentation ℓ T).functor.obj
    ((finiteConstantScalarExtension (Profinite.padicAlgClRingObj ℓ) T).obj P)

private theorem scalarSections_monoidal_eq :
    scalarSections_laxMonoidal.{u} =
      sectionsMonoidal (A := Ab.{u + 1}) (coherentTopology Profinite.{u})
        (T := Profinite.of PUnit.{u + 1}) := by
  let := sectionsMonoidal (A := Ab.{u + 1}) (coherentTopology Profinite.{u})
    (T := Profinite.of PUnit.{u + 1})
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  have : adj.IsMonoidal := inferInstance
  apply Functor.LaxMonoidal.ext
  · exact (Adjunction.IsMonoidal.leftAdjoint_ε (adj := adj)).symm
  · funext X Y
    exact (Adjunction.IsMonoidal.leftAdjoint_μ (adj := adj) X Y).symm

private noncomputable def internalRegularCoordinates (K : Type*) [Ring K] :
    (internalToModule K).obj (Mod.regular (AddCommGrpCat.of K)) ≃ₗ[K] K where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def scalarRegularIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (finiteConstantScalarExtension Λ X).obj (Mod.regular (scalarRingObj Λ)) ≅
      Mod.regular (condensedRingObj Λ X) :=
  (Mod.extendScalars (scalarCoefficientHom Λ X)).mapIso
      (Mod.isoMk (Iso.refl _) (by simp)) ≪≫
    Mod.regularExtensionIso (scalarCoefficientHom Λ X)

section

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]

private instance scalarConstant_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (scalarConstant X) := by
  have : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
    pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
  unfold scalarConstant upperStarFromPoint
  infer_instance

private instance scalarExtension_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (finiteConstantScalarExtension Λ X) := by
  unfold finiteConstantScalarExtension
  infer_instance

private instance scalarExtension_additive (X : Scheme.{u}) :
    (finiteConstantScalarExtension Λ X).Additive := by
  have : PreservesBinaryBiproducts (finiteConstantScalarExtension Λ X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

end

private noncomputable def scalarFreeIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (n : ℕ) :
    (finiteConstantScalarExtension Λ X).obj (Mod.finiteFree (scalarRingObj Λ) n) ≅
      Mod.finiteFree (condensedRingObj Λ X) n :=
  (finiteConstantScalarExtension Λ X).mapBiproduct
      (fun _ : Fin n ↦ Mod.regular (scalarRingObj Λ)) ≪≫
    biproduct.mapIso (fun _ ↦ scalarRegularIso Λ X)

section

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]

private theorem localModel_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨h⟩⟩ := hU i
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (U.f i)).mapIso e.symm ≪≫ h⟩⟩

private theorem stratified_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ X N := by
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun a ↦ localModel_iso
    ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩

private theorem constructible_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split at hM
  · rw [ite_eq_left ‹_›]
    exact stratified_iso e hM
  · rw [ite_eq_right ‹_›]
    exact fun U hU ↦ stratified_iso
      ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)

end

private theorem scalarQbar_monObj (ℓ : ℕ) [Fact ℓ.Prime] :
    (scalarSections.{u}).monObjObj (Profinite.padicAlgClRingObj ℓ) =
      AddCommGrpCat.ringMonObj
        (ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ
          (Profinite.of PUnit.{u + 1}))) := by
  rw [scalarSections_monoidal_eq]
  apply MonObj.ext
  let R := Profinite.padicAlgClCondensedRing.{u} ℓ
  let : MonObj ((Profinite.padicAlgClRingObj ℓ).obj) := R.obj.monObjCompForget₂
  exact congr_app (Sheaf.μ_comp_map_mul (Profinite.padicAlgClRingObj ℓ))
    (Opposite.op (Profinite.of PUnit.{u + 1}))

private noncomputable def scalarQbarConstants (ℓ : ℕ) [Fact ℓ.Prime] :
    ULift.{u + 1} (PadicAlgCl ℓ) ≃+*
      ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ
        (Profinite.of PUnit.{u + 1})) where
  toFun x := ULift.up ⟨ContinuousMap.const _ x.down,
    ℚ_[ℓ]⟮x.down⟯,
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x.down),
    fun _ ↦ IntermediateField.mem_adjoin_simple_self _ _⟩
  invFun f := ULift.up (f.down.1 PUnit.unit)
  left_inv _ := rfl
  right_inv f := by
    apply ULift.ext
    apply Subtype.ext
    ext y
    exact congrArg f.down.1 (Subsingleton.elim PUnit.unit y)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private noncomputable def scalarQbarHom (ℓ : ℕ) [Fact ℓ.Prime] :
    AddCommGrpCat.of (ULift.{u + 1} (PadicAlgCl ℓ)) ⟶
      scalarRingObj (Profinite.padicAlgClRingObj ℓ) :=
  (scalarQbarConstants.{u} ℓ).toAddEquiv.toAddCommGrpIso.hom

private instance scalarQbarHom_isIso (ℓ : ℕ) [Fact ℓ.Prime] :
    IsIso (scalarQbarHom.{u} ℓ) := by
  unfold scalarQbarHom
  infer_instance

private instance scalarQbarHom_isMonHom (ℓ : ℕ) [Fact ℓ.Prime] :
    IsMonHom (scalarQbarHom.{u} ℓ) := by
  change @IsMonHom _ _ _ _ _ _
    ((scalarSections.{u}).monObjObj (Profinite.padicAlgClRingObj ℓ)) (scalarQbarHom.{u} ℓ)
  rw [scalarQbar_monObj.{u}]
  exact AddCommGrpCat.isMonHom_ofHom_ringHom (scalarQbarConstants.{u} ℓ).toRingHom

set_option backward.isDefEq.respectTransparency false in
private theorem scalarQbar_finitelyPresented_isFree (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Mod Ab.{u + 1} (scalarRingObj (Profinite.padicAlgClRingObj ℓ)))
    (hP : Mod.IsFinitelyPresented (scalarRingObj (Profinite.padicAlgClRingObj ℓ)) P) :
    Mod.IsFree (scalarRingObj (Profinite.padicAlgClRingObj ℓ)) P := by
  classical
  let K := ULift.{u + 1} (PadicAlgCl ℓ)
  let R := scalarRingObj (Profinite.padicAlgClRingObj ℓ)
  let φ := scalarQbarHom ℓ
  let Q := Mod.comap φ ⋙ internalToModule K
  have : (Mod.comap φ).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  have : Q.IsEquivalence := by dsimp only [Q]; infer_instance
  have : Q.Additive := by
    have : (internalToModule K).Additive := ⟨by intros; rfl⟩
    dsimp only [Q]
    infer_instance
  let r : (Mod.comap φ).obj (Mod.regular R) ≅ Mod.regular (AddCommGrpCat.of K) :=
    (Mod.comapCongr (by simp : inv (inv φ) = φ)).symm.app _ ≪≫
      Mod.regularIsoOfIsIso (inv φ)
  let b : Q.obj (Mod.regular R) ≃ₗ[K] K :=
    ((internalToModule K).mapIso r).toLinearEquiv.trans
      (internalRegularCoordinates K)
  let c (n : ℕ) := finiteFreeEvaluationCoords (Mod.regular R) Q b n
  obtain ⟨n, m, f, ⟨e⟩⟩ := hP
  let eQ : Q.obj P ≅ cokernel (Q.map f) :=
    Q.mapIso e ≪≫ PreservesCokernel.iso Q f
  have : Module.Finite K (Q.obj (Mod.finiteFree R n)) :=
    Module.Finite.of_injective (c n).toLinearMap (c n).injective
  have : Module.Finite K (cokernel (Q.map f) : ModuleCat K) :=
    Module.Finite.equiv (ModuleCat.cokernelIsoRangeQuotient (Q.map f)).toLinearEquiv.symm
  have : Module.Finite K (Q.obj P) := Module.Finite.equiv eQ.toLinearEquiv.symm
  let B := Module.finBasis K (Q.obj P)
  refine ⟨Module.finrank K (Q.obj P), ⟨Q.preimageIso ?_⟩⟩
  exact (B.equivFun.trans (c _).symm).toModuleIso

private abbrev nativeInternal (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u}) :=
  AdicSheaf.forgetAb ℓ T ⋙ Mod.comap (nativeModuleCoefficientIso ℓ T).hom

private instance nativeInternal_isEquivalence (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) : (nativeInternal ℓ T).IsEquivalence := by
  have : (AdicSheaf.forgetAb ℓ T).IsEquivalence :=
    nativeScalarForgetting_isEquivalence ℓ T
  have : (Mod.comap (nativeModuleCoefficientIso ℓ T).hom).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso
      (nativeModuleCoefficientIso ℓ T).hom).isEquivalence_functor
  dsimp only [nativeInternal]
  infer_instance

private instance nativeToOrdinary_isEquivalence (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) : (nativeToOrdinaryModules ℓ T).IsEquivalence := by
  change (nativeInternal ℓ T ⋙ (nativeOrdinaryPresentation ℓ T).functor).IsEquivalence
  infer_instance

private instance nativeInternal_additive (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) : (nativeInternal ℓ T).Additive := by
  refine ⟨?_⟩
  intros
  rfl

private instance nativeToOrdinary_additive (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) : (nativeToOrdinaryModules ℓ T).Additive := by
  refine ⟨?_⟩
  intros
  rfl

private noncomputable def nativeInternalRegularIso (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) :
    (nativeInternal ℓ T).obj (Mod.regular (adicConstantSheaf ℓ T)) ≅
      Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T) :=
  (Mod.comap (nativeModuleCoefficientIso ℓ T).hom).mapIso
    (Mod.isoMk (Iso.refl _) (by simp [Mod.act])) ≪≫
      (Mod.regularIsoComapRegular (nativeModuleCoefficientIso ℓ T).hom).symm

private noncomputable def nativeInternalFreeIso (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) (r : ℕ) :
    (nativeInternal ℓ T).obj (Mod.finiteFree (adicConstantSheaf ℓ T) r) ≅
      Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T) r :=
  (nativeInternal ℓ T).mapBiproduct _ ≪≫
    biproduct.mapIso fun _ ↦ nativeInternalRegularIso ℓ T

private theorem nativeInternalScalarModel (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u})
    (P : Mod Ab.{u + 1} (scalarRingObj (Profinite.padicAlgClRingObj ℓ)))
    (hP : Mod.IsFinitelyPresented (scalarRingObj (Profinite.padicAlgClRingObj ℓ)) P) :
    ∃ r : ℕ, Nonempty ((nativeInternal ℓ T).obj
      (Mod.finiteFree (adicConstantSheaf ℓ T) r) ≅
        (finiteConstantScalarExtension (Profinite.padicAlgClRingObj ℓ) T).obj P) := by
  obtain ⟨r, ⟨e⟩⟩ := scalarQbar_finitelyPresented_isFree ℓ P hP
  exact ⟨r, ⟨nativeInternalFreeIso ℓ T r ≪≫
    (scalarFreeIso (Profinite.padicAlgClRingObj ℓ) T r).symm ≪≫
      (finiteConstantScalarExtension (Profinite.padicAlgClRingObj ℓ) T).mapIso e.symm⟩⟩

private theorem nativeInternalFreeModel (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) (r : ℕ) :
    ∃ P : Mod Ab.{u + 1} (scalarRingObj (Profinite.padicAlgClRingObj ℓ)),
      Mod.IsFinitelyPresented (scalarRingObj (Profinite.padicAlgClRingObj ℓ)) P ∧
      Nonempty ((nativeInternal ℓ T).obj (Mod.finiteFree (adicConstantSheaf ℓ T) r) ≅
        (finiteConstantScalarExtension (Profinite.padicAlgClRingObj ℓ) T).obj P) := by
  let R := scalarRingObj (Profinite.padicAlgClRingObj ℓ)
  refine ⟨Mod.finiteFree R r, ?_, ⟨nativeInternalFreeIso ℓ T r ≪≫
    (scalarFreeIso (Profinite.padicAlgClRingObj ℓ) T r).symm⟩⟩
  exact ⟨r, r, 0, ⟨(cokernelZeroIsoTarget (X := Mod.finiteFree R r)
    (Y := Mod.finiteFree R r)).symm⟩⟩

private noncomputable def nativeInternalRestrictionIso (ℓ : ℕ) [Fact ℓ.Prime]
    {S T : Scheme.{u}} (h : S ⟶ T) :
    adicUpperStar ℓ h ⋙ nativeInternal ℓ S ≅
      nativeInternal ℓ T ⋙ CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) h :=
  (nativeScalarForgetting_pullbackIso ℓ h).some

private noncomputable def nativeOrdinaryRestrictionIso (ℓ : ℕ) [Fact ℓ.Prime]
    {S T : Scheme.{u}} (h : S ⟶ T) :
    adicUpperStar ℓ h ⋙ nativeToOrdinaryModules ℓ S ≅
      nativeToOrdinaryModules ℓ T ⋙ ordinaryModuleRestriction ℓ h :=
  Functor.isoWhiskerRight (nativeInternalRestrictionIso ℓ h)
      (nativeOrdinaryPresentation ℓ S).functor ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (nativeInternal ℓ T)
      (nativeOrdinaryPresentation ℓ T).unitIso)
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) h ⋙
        (nativeOrdinaryPresentation ℓ S).functor)

private noncomputable def ordinaryInternalCounit (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) (M : AdicSheaf ℓ T) :
    (nativeOrdinaryPresentation ℓ T).inverse.obj ((nativeToOrdinaryModules ℓ T).obj M) ≅
      (nativeInternal ℓ T).obj M :=
  (nativeOrdinaryPresentation ℓ T).unitIso.symm.app _

private noncomputable def ordinaryInternalRestrictionIso (ℓ : ℕ) [Fact ℓ.Prime]
    {S T : Scheme.{u}} (h : S ⟶ T) (M : AdicSheaf ℓ T) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) h).obj
        ((nativeOrdinaryPresentation ℓ T).inverse.obj
          ((nativeToOrdinaryModules ℓ T).obj M)) ≅
      (nativeInternal ℓ S).obj ((adicUpperStar ℓ h).obj M) :=
  (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) h).mapIso
    (ordinaryInternalCounit ℓ T M) ≪≫ (nativeInternalRestrictionIso ℓ h).symm.app M

private theorem nativeSameCover (ℓ : ℕ) [Fact ℓ.Prime]
    (Z : Scheme.{u}) (M : AdicSheaf ℓ Z)
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Z) :
    HasFiniteConstantLocalModelOnCover (Profinite.padicAlgClRingObj ℓ)
        ((nativeOrdinaryPresentation ℓ Z).inverse.obj
          ((nativeToOrdinaryModules ℓ Z).obj M)) 𝒰 ↔
      ∀ i : 𝒰.I₀, ∃ r : ℕ, Nonempty ((adicUpperStar ℓ (𝒰.f i)).obj M ≅
        Mod.finiteFree (adicConstantSheaf ℓ (𝒰.X i)) r) := by
  constructor
  · intro H i
    obtain ⟨P, hP, ⟨e⟩⟩ := H i
    obtain ⟨r, ⟨f⟩⟩ := nativeInternalScalarModel ℓ (𝒰.X i) P hP
    exact ⟨r, ⟨(nativeInternal ℓ (𝒰.X i)).preimageIso
      ((ordinaryInternalRestrictionIso ℓ (𝒰.f i) M).symm ≪≫ e ≪≫ f.symm)⟩⟩
  · intro H i
    obtain ⟨r, ⟨e⟩⟩ := H i
    obtain ⟨P, hP, ⟨f⟩⟩ := nativeInternalFreeModel ℓ (𝒰.X i) r
    exact ⟨P, hP, ⟨ordinaryInternalRestrictionIso ℓ (𝒰.f i) M ≪≫
      (nativeInternal ℓ (𝒰.X i)).mapIso e ≪≫ f⟩⟩

private theorem nativeLisse_iff_cover (ℓ : ℕ) [Fact ℓ.Prime]
    (Z : Scheme.{u}) (M : AdicSheaf ℓ Z) :
    IsAdicLisseSheaf M ↔
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Z,
        ∀ i : 𝒰.I₀, ∃ r : ℕ, Nonempty ((adicUpperStar ℓ (𝒰.f i)).obj M ≅
          Mod.finiteFree (adicConstantSheaf ℓ (𝒰.X i)) r) := by
  have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
    inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
  constructor
  · rintro ⟨R, hR, H⟩
    obtain ⟨V, hV⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hR
    let U := V.restrictIndexOfSmall.{u}
    refine ⟨U, fun i ↦ H (U.f i) ?_⟩
    rw [hV]
    exact V.presieve₀_f (Precoverage.ZeroHypercover.Small.restrictFun V i)
  · rintro ⟨U, H⟩
    refine ⟨U.presieve₀, U.mem₀, ?_⟩
    rintro V f ⟨i⟩
    exact H i

private theorem nativeLocalModel (ℓ : ℕ) [Fact ℓ.Prime]
    (Z : Scheme.{u}) (M : AdicSheaf ℓ Z) :
    HasFiniteConstantLocalModel (Profinite.padicAlgClRingObj ℓ) Z
      ((nativeOrdinaryPresentation ℓ Z).inverse.obj
        ((nativeToOrdinaryModules ℓ Z).obj M)) ↔ IsAdicLisseSheaf M := by
  rw [finiteConstantLocalModel_iff_exists_cover, nativeLisse_iff_cover]
  exact exists_congr fun U ↦ nativeSameCover ℓ Z M U

private theorem nativeSameStratification (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) (M : AdicSheaf ℓ T) (S : Scheme.Stratification T) :
    (∀ a : Fin S.n, HasFiniteConstantLocalModel (Profinite.padicAlgClRingObj ℓ)
      (S.domain a) ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
        (S.immersion a)).obj ((nativeOrdinaryPresentation ℓ T).inverse.obj
          ((nativeToOrdinaryModules ℓ T).obj M)))) ↔
      ∀ a : Fin S.n, IsAdicLisseSheaf ((adicUpperStar ℓ (S.immersion a)).obj M) := by
  apply forall_congr'
  intro a
  let e := ordinaryInternalRestrictionIso ℓ (S.immersion a) M ≪≫
    (ordinaryInternalCounit ℓ (S.domain a) ((adicUpperStar ℓ (S.immersion a)).obj M)).symm
  exact ⟨fun H ↦ (nativeLocalModel ℓ _ _).mp (localModel_iso e H),
    fun H ↦ localModel_iso e.symm ((nativeLocalModel ℓ _ _).mpr H)⟩

private theorem nativeStratification_iff (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) (M : AdicSheaf ℓ T) :
    IsAdicStratifiedLisseSheaf M ↔
      ∃ S : Scheme.Stratification T,
        ∀ a : Fin S.n, IsAdicLisseSheaf ((adicUpperStar ℓ (S.immersion a)).obj M) := by
  classical
  constructor
  · rintro ⟨ι, hι, Z, j, hj, hc, H, hM⟩
    have := hι
    let := Fintype.ofFinite ι
    let e := (Fintype.equivFin ι).symm
    let S : Scheme.Stratification T :=
      { n := Fintype.card ι
        stratum := fun a ↦ Set.range (j (e a)).base
        isLocallyClosed_stratum := fun a ↦ by
          have := hj (e a)
          exact (j (e a)).isLocallyClosed_range
        isConstructible_stratum := fun a ↦ hc (e a)
        iUnion_stratum_eq_univ := by
          apply Set.eq_univ_of_forall
          intro x
          obtain ⟨a, ha, _⟩ := H x
          refine Set.mem_iUnion.mpr ⟨e.symm a, ?_⟩
          rw [e.apply_symm_apply]
          exact ha
        pairwise_disjoint_stratum := by
          intro a b hab
          apply Set.disjoint_left.mpr
          intro x ha hb
          have heq := (H x).unique ha hb
          exact hab (e.injective heq)
        domain := fun a ↦ Z (e a)
        immersion := fun a ↦ j (e a)
        isImmersion := fun a ↦ hj (e a)
        range_immersion := fun _ ↦ rfl }
    exact ⟨S, fun a ↦ hM (e a)⟩
  · rintro ⟨S, H⟩
    refine ⟨Fin S.n, inferInstance, S.domain, S.immersion, S.isImmersion,
      fun a ↦ ?_, fun x ↦ ?_, H⟩
    · rw [S.range_immersion]
      exact S.isConstructible_stratum a
    · have hx : x ∈ ⋃ a, S.stratum a := by rw [S.iUnion_stratum_eq_univ]; trivial
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
      refine ⟨a, ?_, fun b hb ↦ ?_⟩
      · change x ∈ Set.range (S.immersion a).base
        rwa [S.range_immersion a]
      change x ∈ Set.range (S.immersion b).base at hb
      rw [S.range_immersion b] at hb
      by_contra hba
      exact Set.disjoint_left.mp (S.pairwise_disjoint_stratum hba) hb ha

private theorem nativeConstructibility (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] (M : AdicSheaf ℓ T) :
    IsAdicConstructibleSheaf M ↔
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) T
        ((nativeOrdinaryPresentation ℓ T).inverse.obj
          ((nativeToOrdinaryModules ℓ T).obj M)) := by
  classical
  rw [IsConstantModelConstructible, ite_eq_left ⟨inferInstance, inferInstance⟩]
  change IsAdicConstructibleSheaf M ↔ ∃ S, _
  constructor
  · intro H
    obtain ⟨S, hS⟩ := (nativeStratification_iff ℓ T M).mp H.isAdicStratifiedLisseSheaf
    exact ⟨S, (nativeSameStratification ℓ T M S).mpr hS⟩
  · rintro ⟨S, hS⟩
    exact ((nativeStratification_iff ℓ T M).mpr
      ⟨S, (nativeSameStratification ℓ T M S).mp hS⟩).isAdicConstructibleSheaf

/-- The native/ordinary comparison, including its normalization, exactness, restrictions,
finite scalar models on the same covers, constructibility, and derived support intervals. -/
theorem nativeModuleConstructibilityComparison
    (k₀ k : Type u) [Field k₀] [Finite k₀] [Field k] [Algebra k₀ k]
    [IsAlgClosure k₀ k] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k₀)
    (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of k))]
    [IsSeparated (T ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k))] :
    ∃ E : AdicSheaf ℓ T ≌ NativeOrdinaryModules ℓ T,
      E.functor = nativeToOrdinaryModules ℓ T ∧
      E.functor ⋙ SheafOfModules.toSheaf _ =
        AdicSheaf.forget T ⋙ weilCoefficientsForgetAb ℓ T ∧
      (PreservesFiniteLimits E.functor ∧ PreservesFiniteColimits E.functor ∧
        PreservesFiniteLimits E.inverse ∧ PreservesFiniteColimits E.inverse) ∧
      (∀ (Z : Scheme.{u}) (h : Z ⟶ T) [IsImmersion h],
        (nativeToOrdinaryModules ℓ Z).IsEquivalence ∧
        Nonempty (adicUpperStar ℓ h ⋙ nativeToOrdinaryModules ℓ Z ≅
          E.functor ⋙ ordinaryModuleRestriction ℓ h) ∧
        (∀ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Z,
          (∀ i : 𝒰.I₀,
            (nativeToOrdinaryModules ℓ (𝒰.X i)).IsEquivalence ∧
            Nonempty (adicUpperStar ℓ (𝒰.f i) ⋙ nativeToOrdinaryModules ℓ (𝒰.X i) ≅
              nativeToOrdinaryModules ℓ Z ⋙ ordinaryModuleRestriction ℓ (𝒰.f i))) ∧
          (∀ (i : 𝒰.I₀)
              (P : Mod Ab.{u + 1} (scalarRingObj (Profinite.padicAlgClRingObj ℓ))),
            Mod.IsFinitelyPresented (scalarRingObj (Profinite.padicAlgClRingObj ℓ)) P →
              ∃ r : ℕ,
                Nonempty ((nativeToOrdinaryModules ℓ (𝒰.X i)).obj
                  (Mod.finiteFree (adicConstantSheaf ℓ (𝒰.X i)) r) ≅
                    ordinaryScalarModel ℓ (𝒰.X i) P)) ∧
          (∀ (i : 𝒰.I₀) (r : ℕ),
            ∃ P : Mod Ab.{u + 1} (scalarRingObj (Profinite.padicAlgClRingObj ℓ)),
              Mod.IsFinitelyPresented (scalarRingObj (Profinite.padicAlgClRingObj ℓ)) P ∧
              Nonempty ((nativeToOrdinaryModules ℓ (𝒰.X i)).obj
                (Mod.finiteFree (adicConstantSheaf ℓ (𝒰.X i)) r) ≅
                  ordinaryScalarModel ℓ (𝒰.X i) P)) ∧
          (∀ M : AdicSheaf ℓ Z,
            HasFiniteConstantLocalModelOnCover (Profinite.padicAlgClRingObj ℓ)
                ((nativeOrdinaryPresentation ℓ Z).inverse.obj
                  ((nativeToOrdinaryModules ℓ Z).obj M)) 𝒰 ↔
              ∀ i : 𝒰.I₀, ∃ r : ℕ,
                Nonempty ((adicUpperStar ℓ (𝒰.f i)).obj M ≅
                  Mod.finiteFree (adicConstantSheaf ℓ (𝒰.X i)) r)))) ∧
      (∀ (M : AdicSheaf ℓ T) (S : Scheme.Stratification T),
        (∀ a : Fin S.n,
          HasFiniteConstantLocalModel (Profinite.padicAlgClRingObj ℓ) (S.domain a)
            ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (S.immersion a)).obj
              ((nativeOrdinaryPresentation ℓ T).inverse.obj (E.functor.obj M)))) ↔
          ∀ a : Fin S.n, IsAdicLisseSheaf ((adicUpperStar ℓ (S.immersion a)).obj M)) ∧
      (∀ M : AdicSheaf ℓ T,
        IsAdicConstructibleSheaf M ↔
          IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) T
            ((nativeOrdinaryPresentation ℓ T).inverse.obj (E.functor.obj M))) ∧
      (∃ D : DerivedCategory (AdicSheaf ℓ T) ≌ DerivedCategory (NativeOrdinaryModules ℓ T),
        Nonempty (E.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q ≅ DerivedCategory.Q ⋙ D.functor) ∧
        (∀ q : ℤ, Nonempty (D.functor ⋙ DerivedCategory.homologyFunctor _ q ≅
          DerivedCategory.homologyFunctor _ q ⋙ E.functor)) ∧
        (∀ (K : DerivedCategory (AdicSheaf ℓ T)) (a b : ℤ),
          (∀ q : ℤ, q < a ∨ b < q →
              IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) ↔
            ∀ q : ℤ, q < a ∨ b < q →
              IsZero ((DerivedCategory.homologyFunctor _ q).obj (D.functor.obj K))) ∧
        (∀ K : DerivedCategory (AdicSheaf ℓ T),
          (DerivedCategory.TStructure.t.bounded K ∧ ∀ q : ℤ,
              IsAdicConstructibleSheaf ((DerivedCategory.homologyFunctor _ q).obj K)) ↔
            (DerivedCategory.TStructure.t.bounded (D.functor.obj K) ∧ ∀ q : ℤ,
              IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) T
                ((nativeOrdinaryPresentation ℓ T).inverse.obj
                  ((DerivedCategory.homologyFunctor _ q).obj (D.functor.obj K)))))) := by
  classical
  have _ := hℓ
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace
    (T ↘ Spec (CommRingCat.of k))
  have : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated
    (T ↘ Spec (CommRingCat.of k))
  let E := (nativeToOrdinaryModules ℓ T).asEquivalence
  have : E.functor.Additive := nativeToOrdinary_additive ℓ T
  have : E.inverse.Additive := Equivalence.inverse_additive E
  refine ⟨E, rfl, rfl, ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    ?_, nativeSameStratification ℓ T, nativeConstructibility ℓ T, ?_⟩
  · intro Z h _
    refine ⟨inferInstance, ⟨nativeOrdinaryRestrictionIso ℓ h⟩, fun U ↦ ?_⟩
    refine ⟨fun i ↦ ⟨inferInstance, ⟨nativeOrdinaryRestrictionIso ℓ (U.f i)⟩⟩,
      ?_, ?_, fun M ↦ nativeSameCover ℓ Z M U⟩
    · intro i P hP
      obtain ⟨r, ⟨e⟩⟩ := nativeInternalScalarModel ℓ (U.X i) P hP
      exact ⟨r, ⟨(nativeOrdinaryPresentation ℓ (U.X i)).functor.mapIso e⟩⟩
    · intro i r
      obtain ⟨P, hP, ⟨e⟩⟩ := nativeInternalFreeModel ℓ (U.X i) r
      exact ⟨P, hP, ⟨(nativeOrdinaryPresentation ℓ (U.X i)).functor.mapIso e⟩⟩
  · let D := E.mapDerivedCategory
    refine ⟨D, ⟨E.functor.mapDerivedCategoryFactors.symm⟩,
      fun q ↦ ⟨(E.functor.mapDerivedCategoryHomologyFunctorIso q).symm⟩, ?_, ?_⟩
    · intro K a b
      constructor
      · intro H q hq
        exact (E.functor.map_isZero (H q hq)).of_iso
          ((E.functor.mapDerivedCategoryHomologyFunctorIso q).app K).symm
      · intro H q hq
        exact E.functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
          (H q hq)
    · intro K
      constructor
      · rintro ⟨hK, H⟩
        refine ⟨E.functor.bounded_mapDerivedCategory_obj hK, fun q ↦ ?_⟩
        apply constructible_iso
          ((nativeOrdinaryPresentation ℓ T).inverse.mapIso
            ((E.functor.mapDerivedCategoryHomologyFunctorIso q).app K))
        exact (nativeConstructibility ℓ T _).mp (H q)
      · rintro ⟨hK, H⟩
        refine ⟨E.functor.bounded_of_bounded_mapDerivedCategory_obj hK, fun q ↦ ?_⟩
        apply (nativeConstructibility ℓ T _).mpr
        exact constructible_iso
          ((nativeOrdinaryPresentation ℓ T).inverse.mapIso
            ((E.functor.mapDerivedCategoryHomologyFunctorIso q).app K).symm) (H q)

end AlgebraicGeometry.ProEtale
