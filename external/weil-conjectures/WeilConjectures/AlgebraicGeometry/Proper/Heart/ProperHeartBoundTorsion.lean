/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.CategoryTheory.ProEtaleCoefficients.RegularScalarExtensionMultiplication
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseExtensionConstructible
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingPullbackFixed
import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.IntegralReductionTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.AlgebraicGeometry.Proper.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianEvaluationColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Torsion reductions of locally closed integral lattices

The ordinary relative tensor with the actual quotient module is the canonical quotient
by the uniformizer power. The scalar equations in the origin predicate retain its module
structure when comparing with fixed finite-coefficient sheaves.
-/

@[expose] public noncomputable section

set_option linter.unusedVariables false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]

/-- Multiplication by an actual integral scalar on the continuous condensed integer sheaf. -/
def torsionIntegerMultiply (b : Padic.coefficientExtensionIntegers ℓ E) :
    End (DerivedNakayama.integerRing ℓ E) :=
  letI := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  .of ⟨{
    app := fun S ↦ AddCommGrpCat.ofHom
      (AddMonoidHom.mulLeft (ULift.up (ContinuousMap.const S.unop b)))
    naturality := fun _ _ _ ↦ rfl }⟩

/-- The underlying additive scalar endomorphism, using the pulled-back scalar and the
specified internal module action. -/
def torsionScalar {X : Scheme.{u}}
    (M : pulledBackModuleObjects (DerivedNakayama.integerRing ℓ E) X)
    (b : Padic.coefficientExtensionIntegers ℓ E) : End M.X :=
  .of ((λ_ M.X).inv ≫
    ((η[condensedRingObj (DerivedNakayama.integerRing ℓ E) X] ≫
      (upperStarFromPoint X).map (torsionIntegerMultiply ℓ E b).asHom) ▷ M.X) ≫
      Mod.act M.X)

/-- Scalar multiplication on a fixed-coefficient module sheaf, with the given scalar action. -/
def torsionFixedScalar {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {B : Type (u + 1)} [CommRing B]
    (G : Sheaf J (ModuleCat.{u + 1} B)) (b : B) : End G :=
  .of ⟨{
    app := fun U ↦ ModuleCat.ofHom (b • LinearMap.id)
    naturality := fun _ _ f ↦ by
      ext m
      exact ((G.obj.map f).hom.map_smul b m).symm }⟩

section Reduction

open CondensedRing

attribute [local irreducible] DerivedCategory.monoidalClosed Mod.monoidalClosed
  upperStarFromPoint CondensedRing.upperStar CondensedRing.upperStarComp
  Mod.monoidalCategoryStruct ObjectProperty.flat

private def pointPullbackIso {S X : Scheme.{u}} (a : S ⟶ X)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (P : Mod (Sheaf (coherentTopology Profinite.{u})
      Ab.{u + 1}) Λ) :
    (CondensedRing.upperStar Λ a).obj (((upperStarFromPoint X).mapMod Λ).obj P) ≅
      ((upperStarFromPoint S).mapMod Λ).obj P := by
  unfold CondensedRing.upperStar
  let φ := condensedPullbackHom Λ a
  let N := ((upperStarFromPoint S).mapMod Λ).obj P
  let e := (Functor.mapModCompIso (upperStarFromPoint X)
    (upperStar Ab.{u + 1} a) (upperStarFromPointComp a).hom Λ).app P
  exact (Mod.extendScalars φ).mapIso e ≪≫
    (Mod.extendScalarsIsoComapInv φ).app ((Mod.comap φ).obj N) ≪≫
    (Mod.comapEquivalenceOfIsIso φ).unitIso.symm.app N

attribute [local irreducible] generatorExtension generatorRestriction
  tensorRestrictionIso pointPullbackIso
attribute [local instance] generatorRestriction_isIso

private theorem projection_exists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    {a : S ⟶ X} [IsImmersion a] (A : GeneratorFactorization a)
    (B : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (L : pulledBackModuleObjects Λ S) :
    ∃ e : ((generatorExtension Λ A).obj L ⊗ ((upperStarFromPoint X).mapMod Λ).obj B) ≅
      (generatorExtension Λ A).obj (L ⊗ ((upperStarFromPoint S).mapMod Λ).obj B),
      (CondensedRing.upperStar Λ a).map e.hom ≫ (generatorRestriction Λ A).app _ =
      (tensorRestrictionIso (CondensedRing.upperStar Λ a)
        ((asIso (generatorRestriction Λ A)).app L) (pointPullbackIso a Λ B)).hom := by
  have hs : universallySupported Λ a
      ((generatorExtension Λ A).obj L ⊗ ((upperStarFromPoint X).mapMod Λ).obj B) :=
    supported_tensor_left Λ a _ _ (fun g hg ↦ generatorExtension_support Λ A g hg L)
  exact normalized_comparison_of_essImage (generatorExtension Λ A)
    (CondensedRing.upperStar Λ a) (generatorExtension_fullyFaithful Λ A)
    (asIso (generatorRestriction Λ A)) _ _
    ⟨_, generatorExtension_reconstruct Λ A _ hs⟩
    (tensorRestrictionIso (CondensedRing.upperStar Λ a)
      ((asIso (generatorRestriction Λ A)).app L) (pointPullbackIso a Λ B))

section Projection

private def projectionIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
  [IsLocallyNoetherian X] [CompactSpace X]
  {a : S ⟶ X} [IsImmersion a] (A : GeneratorFactorization a)
  (B : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (L : pulledBackModuleObjects Λ S) :=
  Classical.choose (projection_exists Λ (a := a) A B L)

attribute [local irreducible] projectionIso

end Projection

end Reduction

section Origin

open CondensedRing

private local instance (n : ℕ) : TopologicalSpace (Padic.coefficientExtensionRing ℓ E n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  inferInstance

private local instance (n : ℕ) : IsTopologicalRing (Padic.coefficientExtensionRing ℓ E n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  inferInstance

private def scalarIntegerMap (A : Type u) [CommRing A] (b : A) :
    𝟙_ Ab.{u + 1} ⟶ AddCommGrpCat.of (ULift.{u + 1} A) :=
  AddCommGrpCat.ofHom
    { toFun z := z.down • (ULift.up b)
      map_zero' := by simp
      map_add' x y := by simp [add_mul] }

attribute [local irreducible] Mod.monoidalCategoryStruct Mod.monoidalClosed

private theorem point_scalar_constant (n : ℕ)
    (b : Padic.coefficientExtensionIntegers ℓ E) :
    η[DerivedNakayama.integerRing ℓ E] ≫ (torsionIntegerMultiply ℓ E b).asHom ≫
      DerivedNakayama.reductionRing ℓ E n =
    Functor.LaxMonoidal.ε (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
        (scalarIntegerMap (Padic.coefficientExtensionRing ℓ E n)
          (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b)) ≫
      (((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
        _ (DerivedNakayama.quotientRing ℓ E n)).symm
          (FiniteDiscreteOrdinary.pointConstants (Padic.coefficientExtensionRing ℓ E n))) := by
  let := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  let J := coherentTopology Profinite.{u}
  have hc : Functor.LaxMonoidal.ε (constantSheaf J Ab.{u + 1}) = 𝟙 _ := by
    change 𝟙 _ ≫ (presheafToSheaf J Ab.{u + 1}).map (𝟙 _) = 𝟙 _
    exact (Category.id_comp _).trans ((presheafToSheaf J Ab.{u + 1}).map_id _)
  let U := sheafToPresheaf J Ab.{u + 1}
  let g := scalarIntegerMap (Padic.coefficientExtensionRing ℓ E n)
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b)
  apply ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _).injective
  change Functor.LaxMonoidal.ε U ≫
      U.map (η[DerivedNakayama.integerRing ℓ E] ≫ (torsionIntegerMultiply ℓ E b).asHom ≫
        DerivedNakayama.reductionRing ℓ E n) = _
  simp only [Functor.map_comp, ← Category.assoc]
  erw [Sheaf.ε_sheafToPresheaf_comp_map_one_sheafCompose]
  rw [hc, Category.id_comp]
  change _ = (sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _
    ((presheafToSheaf J Ab.{u + 1}).map
      ((Functor.const Profinite.{u}ᵒᵖ).map g) ≫ _)
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
  ext S z
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  dsimp only [U, g, scalarIntegerMap, torsionIntegerMultiply,
    DerivedNakayama.reductionRing, DerivedNakayama.reductionRingSheaf,
    FiniteDiscreteOrdinary.pointConstants]
  simp only [NatTrans.comp_app, AddCommGrpCat.comp_apply]
  rw [Functor.one_compForget₂_app]
  erw [AddCommGrpCat.ringMonObj_one_apply]
  with_unfolding_all
    change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n)
      (b * (z.down : Padic.coefficientExtensionIntegers ℓ E)) =
    z.down • Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b
  simp [map_mul, mul_comm, zsmul_eq_mul]

attribute [local irreducible] upperStarFromPoint torsionIntegerMultiply

private theorem scalar_constant (T : Scheme.{u}) (n : ℕ)
    (b : Padic.coefficientExtensionIntegers ℓ E) :
    η[condensedRingObj (DerivedNakayama.integerRing ℓ E) T] ≫
      (upperStarFromPoint T).map (torsionIntegerMultiply ℓ E b).asHom ≫
      coefficientMap (DerivedNakayama.reductionRing ℓ E n) T =
    Functor.LaxMonoidal.ε (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ≫
      (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).map
        (scalarIntegerMap (Padic.coefficientExtensionRing ℓ E n)
          (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b)) ≫
      FiniteDiscreteOrdinary.canonicalAbelianMap
        (Padic.coefficientExtensionRing ℓ E n) T := by
  let := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  let F := upperStarFromPoint T
  let P := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let Q := constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}
  let g := scalarIntegerMap (Padic.coefficientExtensionRing ℓ E n)
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b)
  let ψ := ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
    _ (DerivedNakayama.quotientRing ℓ E n)).symm
      (FiniteDiscreteOrdinary.pointConstants (Padic.coefficientExtensionRing ℓ E n))
  have hnat := (constantSchemeIso T).hom.naturality g
  change Q.map g ≫ (constantSchemeIso T).hom.app _ =
    (constantSchemeIso T).hom.app _ ≫ F.map (P.map g) at hnat
  have hu := NatTrans.IsMonoidal.unit (τ := (constantSchemeIso T).hom)
  change Functor.LaxMonoidal.ε Q ≫ (constantSchemeIso T).hom.app _ =
    Functor.LaxMonoidal.ε F ≫ F.map (Functor.LaxMonoidal.ε P) at hu
  change Functor.LaxMonoidal.ε F ≫ F.map η[DerivedNakayama.integerRing ℓ E] ≫
      F.map (torsionIntegerMultiply ℓ E b).asHom ≫ F.map (DerivedNakayama.reductionRing ℓ E n) =
    Functor.LaxMonoidal.ε Q ≫ Q.map g ≫ (constantSchemeIso T).hom.app _ ≫ F.map ψ
  erw [reassoc_of% hnat, reassoc_of% hu]
  simp only [← F.map_comp]
  congr 1
  exact congrArg F.map (point_scalar_constant ℓ E n b)

private theorem constant_scalar_section (T : Scheme.{u}) (n : ℕ)
    (b : Padic.coefficientExtensionIntegers ℓ E) (V : T.ProEtᵒᵖ) :
    sfbRegularSection (Scheme.ProEt.topology T) _
      (η[condensedRingObj (DerivedNakayama.integerRing ℓ E) T] ≫
        (upperStarFromPoint T).map (torsionIntegerMultiply ℓ E b).asHom ≫
        coefficientMap (DerivedNakayama.reductionRing ℓ E n) T) V =
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing ℓ E n)))) ≫
        (FiniteDiscreteOrdinary.canonicalAbelianMap
          (Padic.coefficientExtensionRing ℓ E n) T).hom).app V).hom
        (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b)) := by
  rw [scalar_constant]
  unfold sfbRegularSection
  let J := Scheme.ProEt.topology T
  let A := Padic.coefficientExtensionRing ℓ E n
  let a := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b
  let g := scalarIntegerMap A a
  have hc : Functor.LaxMonoidal.ε (constantSheaf J Ab.{u + 1}) = 𝟙 _ := by
    change 𝟙 _ ≫ (presheafToSheaf J Ab.{u + 1}).map (𝟙 _) = 𝟙 _
    exact (Category.id_comp _).trans ((presheafToSheaf J Ab.{u + 1}).map_id _)
  rw [hc, Category.id_comp]
  change (FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app V
      (((constantSheaf J Ab.{u + 1}).map g).hom.app V
        ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (𝟙_ Ab.{u + 1}))).app V
          (ULift.up (1 : ℤ)))) =
    (FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app V
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)))).app V (ULift.up a))
  apply congrArg ((FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app V)
  have h := toSheafify_naturality J
    ((Functor.const T.ProEtᵒᵖ).map g)
  have he := congrArg (fun t ↦ (t.app V).hom (ULift.up (1 : ℤ))) h
  change ((constantSheaf J Ab.{u + 1}).map g).hom.app V
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (𝟙_ Ab.{u + 1}))).app V
        (ULift.up (1 : ℤ))) =
    (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))).app V (ULift.up a)
  change (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))).app V (g.hom (ULift.up (1 : ℤ))) =
    ((constantSheaf J Ab.{u + 1}).map g).hom.app V
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (𝟙_ Ab.{u + 1}))).app V
        (ULift.up (1 : ℤ))) at he
  have hg : g.hom (ULift.up (1 : ℤ)) = ULift.up a := by simp [g, scalarIntegerMap]
  rw [hg] at he
  exact he.symm

attribute [local irreducible] FiniteDiscreteOrdinary.canonicalAbelianMap

private theorem scalar_encoded (T : Scheme.{u}) (n : ℕ)
    (e : FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing ℓ E n) T)
    (M : FiniteDiscreteOrdinary.Internal (Padic.coefficientExtensionRing ℓ E n) T)
    (b : Padic.coefficientExtensionIntegers ℓ E) :
    (torsionScalar ℓ E
      ((Mod.comap (coefficientMap (DerivedNakayama.reductionRing ℓ E n) T)).obj M) b).asHom =
      (sheafCompose (Scheme.ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing ℓ E n))) Ab.{u + 1})).map
        (torsionFixedScalar ((FiniteDiscreteOrdinary.sectionEncoding _ T e.ringIso ⋙
          FiniteDiscreteOrdinary.fixedRestriction _ T).obj M)
          (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b))).asHom := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro m
  change _ = (show M.X.obj.obj V from
    (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b) :
      ULift.{u + 1} (Padic.coefficientExtensionRing ℓ E n)) •
    (show ((FiniteDiscreteOrdinary.sectionEncoding _ T e.ringIso ⋙
      FiniteDiscreteOrdinary.fixedRestriction _ T).obj M).obj.obj V from m))
  rw [FiniteDiscreteOrdinary.encoding_smul]
  change (((λ_ M.X).inv ≫
    ((η[condensedRingObj (DerivedNakayama.integerRing ℓ E) T] ≫
      (upperStarFromPoint T).map (torsionIntegerMultiply ℓ E b).asHom) ▷ M.X) ≫
      (coefficientMap (DerivedNakayama.reductionRing ℓ E n) T ▷ M.X) ≫
      Mod.act M.X).hom.app V).hom m = _
  rw [← comp_whiskerRight_assoc]
  change (Mod.act M.X).hom.app V
    (((λ_ M.X).inv ≫ _ ▷ M.X).hom.app V m) = _
  rw [left_section]
  simp only [Category.assoc]
  erw [constant_scalar_section]
  rfl


end Origin

open CondensedRing


end AlgebraicGeometry.ProEtale
