/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Category.Profinite.AsLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
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
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
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
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

import WeilConjectures.AlgebraicGeometry.Constant.ConstantZModScalarTensor
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.NumberTheory.Padics.IntegersModPow
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistLevels

/-! # Finite levels and integral and rational Tate twist objects

The index n denotes exponent n+1.
The integral levels use the finite quotient tensor with the roots, restricted
along O_X -> B_X. The integral object is their limit in O_X-modules, and the
rational object is its specified extension of scalars. These are the original
constructions re-exported by `ProEtaleTateTwists`, with unchanged data and names.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance 20000] HasLimitsOfShape.has_limit HasColimitsOfShape.has_colimit
attribute [local instance 20000] Sheaf.instHasLimitsOfShape AddCommGrpCat.hasLimitsOfShape

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The finite twist uses the unique unital quotient homomorphism to A.
The positive index r represents the annihilating exponent r+1; its vanishing
on 1 is equivalent to annihilation of every A-module scalar. -/
def spFiniteTwist (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : (ℓ ^ (r + 1) : A) = 0) :=
  Scheme.tateFiniteLine X ℓ A r
    (ZMod.castHom (ringChar.dvd (by simpa only [Nat.cast_pow] using hA)) A)

set_option backward.isDefEq.respectTransparency false in
/-- The two recorded integer-ring models agree as subrings of the fixed finite field. -/
theorem spIntegers_eq (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Padic.coefficientExtensionIntegers ℓ E.1 = (PadicAlgCl.integers ℓ E.1).toSubring := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra (Padic ℓ) E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          norm_algebraMap'] }
  have hmem (x : E.1) : x ∈ Padic.coefficientExtensionIntegers ℓ E.1 ↔
      (Padic.coefficientExtensionAbsoluteValue ℓ E.1) x ≤ 1 :=
    (Padic.coefficientExtensionIntegers_dvr ℓ E.1).choose_spec.1 x
  apply Subring.ext
  intro x
  rw [hmem x]
  change spectralNorm (Padic ℓ) E.1 x ≤ 1 ↔
    ‖algebraMap E.1 (PadicAlgCl ℓ) x‖₊ ≤ 1
  rw [← NormedAlgebra.norm_eq_spectralNorm (Padic ℓ)]
  change ‖algebraMap E.1 (PadicAlgCl ℓ) x‖ ≤ 1 ↔
    ‖algebraMap E.1 (PadicAlgCl ℓ) x‖₊ ≤ 1
  simpa only [NNReal.coe_one, coe_nnnorm] using
    (NNReal.coe_le_coe (r₁ := ‖algebraMap E.1 (PadicAlgCl ℓ) x‖₊) (r₂ := 1))

set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] spEllPointReduction

set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] spEllPointTransition

set_option backward.isDefEq.respectTransparency false in
private theorem spFreeTensor_linear
    {C : Type*} [Category C] [MonoidalCategory C]
    {R B D : C} [MonObj R] [MonObj B] [MonObj D]
    (p : R ⟶ B) [IsMonHom p] (q : R ⟶ D) [IsMonHom q]
    (r : B ⟶ D) [IsMonHom r] (h : p ≫ r = q)
    {U V : C} (v : U ⟶ V) :
    ∃! f : (Mod.comap p).obj ((Mod.free B).obj U) ⟶
        (Mod.comap q).obj ((Mod.free D).obj V), f.hom = r ⊗ₘ v := by
  let f : (Mod.comap p).obj ((Mod.free B).obj U) ⟶
      (Mod.comap q).obj ((Mod.free D).obj V) := Mod.homMk (r ⊗ₘ v) (by
    change (p ▷ (B ⊗ U) ≫ (α_ B B U).inv ≫ MonObj.mul ▷ U) ≫ (r ⊗ₘ v) =
      R ◁ (r ⊗ₘ v) ≫ q ▷ (D ⊗ V) ≫ (α_ D D V).inv ≫ MonObj.mul ▷ V
    have hm : (p ⊗ₘ 𝟙 B) ≫ MonObj.mul ≫ r =
        (q ⊗ₘ r) ≫ MonObj.mul := by
      rw [IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, h, Category.id_comp]
    calc
      _ = (α_ R B U).inv ≫ (((p ⊗ₘ 𝟙 B) ≫ MonObj.mul ≫ r) ⊗ₘ v) := by
        simp only [Category.assoc]
        rw [associator_inv_naturality_left_assoc]
        simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
      _ = (α_ R B U).inv ≫ (((q ⊗ₘ r) ≫ MonObj.mul) ⊗ₘ v) := by rw [hm]
      _ = (q ⊗ₘ (r ⊗ₘ v)) ≫ (α_ D D V).inv ≫ MonObj.mul ▷ V := by
        rw [associator_inv_naturality_assoc]
        simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
      _ = _ := by
        simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, Category.comp_id])
  refine ⟨f, rfl, ?_⟩
  intro g hg
  exact Mod.hom_ext _ _ hg

set_option backward.isDefEq.respectTransparency false in
/-- The finite-level twist is the displayed constant-ring scalar extension. -/
theorem spIntegralTwistLevel_comparison (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    ∃ a : ZMod (ℓ ^ (n + 1)) →+* ULift.{u + 1} (spEllQuotient ℓ E n),
      Nonempty ((spIntegralTwistLevel X ℓ E n).X ≅
        (SheafOfModules.toSheaf _).obj
          (Scheme.tateFiniteLine X ℓ (ULift.{u + 1} (spEllQuotient ℓ E n)) n a)) := by
  let : CommRing (PadicAlgCl.integers ℓ E.1) := inferInstance
  let B := spEllQuotient ℓ E n
  let : CommRing B := Ideal.Quotient.commRing _
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  let : IsTopologicalRing B := DiscreteTopology.topologicalRing
  let : Finite B := (spEllQuotient_finite_continuous ℓ E n).1
  have hB : (ℓ ^ (n + 1) : B) = 0 := by
    have h : (Ideal.Quotient.mk (spTateEllIdeal ℓ E n)) (ℓ ^ (n + 1)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    simpa only [map_pow, map_natCast] using h
  have hB' : ((ℓ ^ (n + 1) : ℕ) : B) = 0 :=
    (Nat.cast_pow ℓ (n + 1)).trans hB
  let : CharP B (ringChar B) := ringChar.charP B
  let b : ZMod (ℓ ^ (n + 1)) →+* B :=
    ZMod.castHom (ringChar.dvd (R := B) hB') B
  let a : ZMod (ℓ ^ (n + 1)) →+* ULift.{u + 1} B :=
    ULift.ringEquiv.symm.toRingHom.comp b
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} B
  obtain ⟨eX, _⟩ := finiteDiscreteSchemeRing_constant.{u} B X eR heR
  obtain ⟨eT⟩ := Scheme.constantZMod_scalarTensor X ℓ n (ULift.{u + 1} B) a
    (Scheme.purTwistRootsModule X ℓ n)
  refine ⟨a, ⟨?_⟩⟩
  exact (eX.symm ⊗ᵢ
    Iso.refl (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1)))) ≪≫ eT

end AlgebraicGeometry.ProEtale
