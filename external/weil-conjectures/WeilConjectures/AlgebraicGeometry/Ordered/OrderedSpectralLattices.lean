/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartOrderedRefinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.StratifiedLattice
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.Algebra.Shrink
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullOrdinaryUnit
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Lisse integral lattices on an ordered stratification

## References

* Bhatt--Scholze, Lemma 6.8.13, first paragraph
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CondensedRing.pullIso CondensedRing.upperStarComp
  CondensedRing.comapUpperStarIso

private structure SmallAlgebraModel (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] where
  carrier : Type
  field : Field carrier
  algebra : @Algebra ℚ_[ℓ] carrier _ field.toSemiring
  finite : @FiniteDimensional ℚ_[ℓ] carrier _ field.toAddCommGroup algebra.toModule
  equiv : @AlgEquiv ℚ_[ℓ] carrier E _ field.toSemiring _ algebra _

private noncomputable def smallAlgebraModel (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    SmallAlgebraModel ℓ E := by
  have : Small.{0} E := Module.Finite.small ℚ_[ℓ] E
  let K := Shrink.{0} E
  let e : K ≃ₐ[ℚ_[ℓ]] E := Shrink.algEquiv ℚ_[ℓ] E
  exact ⟨K, inferInstance, inferInstance, e.symm.toLinearEquiv.finiteDimensional, e⟩

/-- The recorded integral subring is the spectral norm unit ball. -/
private theorem mem_spectral_integers (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (x : E) :
    x ∈ Padic.coefficientExtensionIntegers ℓ E ↔ spectralNorm ℚ_[ℓ] E x ≤ 1 := by
  exact (Padic.coefficientExtensionIntegers_dvr ℓ E).choose_spec.1 x

/-- A coefficient equivalence preserves the canonical spectral norm. -/
private theorem spectral_equiv_norm (ℓ : ℕ) [Fact ℓ.Prime]
    {K : Type} [Field K] [Algebra ℚ_[ℓ] K] [FiniteDimensional ℚ_[ℓ] K]
    {E : Type u} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (e : K ≃ₐ[ℚ_[ℓ]] E) :
    letI := spectralNorm.nontriviallyNormedField ℚ_[ℓ] K
    letI := spectralNorm.nontriviallyNormedField ℚ_[ℓ] E
    ∀ x : K, ‖e x‖ = ‖x‖ := by
  intro x
  change spectralNorm ℚ_[ℓ] E (e x) = spectralNorm ℚ_[ℓ] K x
  simp only [spectralNorm, minpoly.algEquiv_eq]

private noncomputable def spectral_integer_equiv (ℓ : ℕ) [Fact ℓ.Prime]
    {K : Type} [Field K] [Algebra ℚ_[ℓ] K] [FiniteDimensional ℚ_[ℓ] K]
    {E : Type u} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (e : K ≃ₐ[ℚ_[ℓ]] E) :
    Padic.coefficientExtensionIntegers ℓ K ≃+* Padic.coefficientExtensionIntegers ℓ E where
  toFun x := ⟨e x, by
    apply (mem_spectral_integers _ _ _).mpr
    simpa only [spectralNorm, minpoly.algEquiv_eq] using
      (mem_spectral_integers _ _ _).mp x.property⟩
  invFun x := ⟨e.symm x, by
    apply (mem_spectral_integers _ _ _).mpr
    simpa only [spectralNorm, minpoly.algEquiv_eq] using
      (mem_spectral_integers _ _ _).mp x.property⟩
  left_inv x := by ext; exact e.symm_apply_apply x
  right_inv x := by ext; exact e.apply_symm_apply x
  map_mul' x y := by ext; exact e.map_mul x y
  map_add' x y := by ext; exact e.map_add x y

/-- Postcomposition across coefficient universes; both section rings lie in u+1. -/
private noncomputable def small_continuous_ring_iso
    {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    {E : Type u} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
    (e : K ≃+* E) (he : Continuous e) (hi : Continuous e.symm) :
    Profinite.continuousMapRingSheaf.{u} K ≅
      Profinite.continuousMapRingSheafOfUniverse.{u, u} E := by
  let h : Profinite.continuousMapRingSheaf.{u} K ⟶
      Profinite.continuousMapRingSheafOfUniverse.{u, u} E :=
    ⟨{ app := fun _ ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.toRingHom.compLeftContinuous _ he).comp ULift.ringEquiv.toRingHom))
       naturality := fun _ _ _ ↦ rfl }⟩
  let i : Profinite.continuousMapRingSheafOfUniverse.{u, u} E ⟶
      Profinite.continuousMapRingSheaf.{u} K :=
    ⟨{ app := fun _ ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.symm.toRingHom.compLeftContinuous _ hi).comp ULift.ringEquiv.toRingHom))
       naturality := fun _ _ _ ↦ rfl }⟩
  refine ⟨h, i, ?_, ?_⟩
  · ext X x
    apply ULift.ext
    ext y
    exact e.symm_apply_apply (x.down y)
  · ext X x
    apply ULift.ext
    ext y
    exact e.apply_symm_apply (x.down y)

private theorem small_continuous_square
    {K K' : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [CommRing K'] [TopologicalSpace K'] [IsTopologicalRing K']
    {E E' : Type u} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
    [CommRing E'] [TopologicalSpace E'] [IsTopologicalRing E']
    (e : K ≃+* E) (he : Continuous e) (hei : Continuous e.symm)
    (e' : K' ≃+* E') (he' : Continuous e') (hei' : Continuous e'.symm)
    (f : K →+* K') (hf : Continuous f) (g : E →+* E') (hg : Continuous g)
    (w : ∀ x, e' (f x) = g (e x)) :
    Profinite.continuousMapRingSheafMap.{u} f hf ≫
        (small_continuous_ring_iso e' he' hei').hom =
      (small_continuous_ring_iso e he hei).hom ≫
        Profinite.continuousMapRingSheafMapOfUniverse.{u, u} g hg := by
  ext X x
  apply ULift.ext
  ext y
  exact w (x.down y)

private structure ContinuousRingSquare
    (A₀ B₀ A B : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    (a₀ : A₀ ⟶ B₀) (a : A ⟶ B) where
  integral : A₀ ≅ A
  rational : B₀ ≅ B
  commutes : a₀ ≫ rational.hom = integral.hom ≫ a

private noncomputable def spectralCoefficientSquare (ℓ : ℕ) [Fact ℓ.Prime]
    {K : Type} [Field K] [Algebra ℚ_[ℓ] K] [FiniteDimensional ℚ_[ℓ] K]
    {E : Type u} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (e : K ≃ₐ[ℚ_[ℓ]] E) :
    letI := spectralNorm.nontriviallyNormedField ℚ_[ℓ] K
    letI := spectralNorm.nontriviallyNormedField ℚ_[ℓ] E
    ContinuousRingSquare
      (Profinite.continuousMapRingSheaf.{u} (Padic.coefficientExtensionIntegers ℓ K))
      (Profinite.continuousMapRingSheaf.{u} K)
      (Profinite.continuousMapRingSheafOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers ℓ E))
      (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
      (Profinite.continuousMapRingSheafMap
        (Padic.coefficientExtensionIntegers ℓ K).subtype continuous_subtype_val)
      (Profinite.continuousMapRingSheafMapOfUniverse
        (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val) := by
  let := spectralNorm.nontriviallyNormedField ℚ_[ℓ] K
  let := spectralNorm.nontriviallyNormedField ℚ_[ℓ] E
  have he : Isometry e := AddMonoidHomClass.isometry_of_norm e (spectral_equiv_norm ℓ e)
  let ee : K ≃ᵢ E := ⟨e.toEquiv, he⟩
  have hi : Continuous e.symm := ee.symm.continuous
  let ei := spectral_integer_equiv ℓ e
  have hei : Continuous ei := (he.continuous.comp continuous_subtype_val).subtype_mk _
  have hii : Continuous ei.symm := (hi.comp continuous_subtype_val).subtype_mk _
  exact ⟨small_continuous_ring_iso ei hei hii,
    small_continuous_ring_iso e.toRingEquiv he.continuous hi,
    small_continuous_square ei hei hii e.toRingEquiv he.continuous hi
      (Padic.coefficientExtensionIntegers ℓ K).subtype continuous_subtype_val
      (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val (fun _ ↦ rfl)⟩

private theorem lisse_iff_locallyFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsLisseCoefficientModule Λ M ↔ CondensedRing.LocallyFree (condensedRingObj Λ X) M := by
  constructor
  · rintro ⟨U, hU⟩
    refine ⟨U, fun i ↦ ?_⟩
    let φ := condensedPullbackHom Λ (U.f i)
    apply free_of_comap (inv φ)
    exact free_of_iso (hU i) ((Mod.extendScalarsIsoComapInv φ).app _)
  · rintro ⟨U, hU⟩
    refine ⟨U, fun i ↦ ?_⟩
    let φ := condensedPullbackHom Λ (U.f i)
    exact free_of_iso (free_comap (inv φ) (hU i))
      ((Mod.extendScalarsIsoComapInv φ).app _).symm

private theorem lisse_comap
    {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] [IsIso a] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (hM : IsLisseCoefficientModule B M) :
    IsLisseCoefficientModule A ((Mod.comap (coefficientMap a X)).obj M) := by
  exact (lisse_iff_locallyFree A _).mpr
    (CondensedRing.locallyFree_comap (coefficientMap a X)
      ((lisse_iff_locallyFree B M).mp hM))

private noncomputable def coefficient_square_transport
    (A₀ B₀ A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A₀] [IsCommMonObj A₀] [MonObj B₀] [IsCommMonObj B₀]
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a₀ : A₀ ⟶ B₀) [IsMonHom a₀] (a : A ⟶ B) [IsMonHom a]
    (r : A₀ ≅ A) [IsMonHom r.hom] (s : B₀ ≅ B) [IsMonHom s.hom]
    (w : a₀ ≫ s.hom = r.hom ≫ a) (X : Scheme.{u}) :
    ((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (coefficientMap s.hom X) ⋙ Mod.comap (coefficientMap a₀ X)) ⋙
        Mod.comap (coefficientMap r.inv X)) ≅ Mod.comap (coefficientMap a X) := by
  refine Functor.isoWhiskerRight
    (Mod.comapComp (coefficientMap a₀ X) (coefficientMap s.hom X)).symm
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (coefficientMap r.inv X)) ≪≫
    (Mod.comapComp (coefficientMap r.inv X)
      (coefficientMap a₀ X ≫ coefficientMap s.hom X)).symm ≪≫ Mod.comapCongr ?_
  rw [← coefficientMap_comp, ← coefficientMap_comp]
  congr 1
  rw [w, r.inv_hom_id_assoc]

private theorem transport_lattice_arrow
    {C₀ D₀ C D : Type*} [Category C₀] [Category D₀] [Category C] [Category D]
    {F₀ : C₀ ⥤ D₀} {G₀ : D₀ ⥤ C₀} (adj₀ : F₀ ⊣ G₀)
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (U : C₀ ≌ C) (V : D₀ ≌ D)
    (e : (V.inverse ⋙ G₀) ⋙ U.functor ≅ G)
    (L : D) (M₀ : C₀) (i : M₀ ⟶ G₀.obj (V.inverse.obj L)) [Mono i]
    [IsIso ((adj₀.homEquiv M₀ (V.inverse.obj L)).symm i)] :
    ∃ j : U.functor.obj M₀ ⟶ G.obj L,
      Mono j ∧ IsIso ((adj.homEquiv _ L).symm j) := by
  let adj' := ((U.symm.toAdjunction.comp adj₀).comp V.toAdjunction).ofNatIsoRight e
  let t := (adj₀.homEquiv M₀ (V.inverse.obj L)).symm i
  let q := F₀.map (U.unitIso.inv.app M₀) ≫ t
  let t' := (V.toAdjunction.homEquiv _ L).symm q
  have hv : V.toAdjunction.homEquiv _ L t' = q :=
    (V.toAdjunction.homEquiv _ L).apply_symm_apply q
  have ht : adj₀.homEquiv M₀ (V.inverse.obj L) t = i :=
    (adj₀.homEquiv _ _).apply_symm_apply i
  have hq : adj₀.homEquiv _ _ q = U.unitIso.inv.app M₀ ≫ i := by
    change adj₀.homEquiv _ _ (F₀.map (U.unitIso.inv.app M₀) ≫ t) = _
    exact (adj₀.homEquiv_naturality_left (U.unitIso.inv.app M₀) t).trans
      (congrArg (fun z ↦ U.unitIso.inv.app M₀ ≫ z) ht)
  have hu : U.symm.toAdjunction.homEquiv _ _ (U.unitIso.inv.app M₀ ≫ i) =
      U.functor.map i := by
    rw [Adjunction.homEquiv_unit]
    change U.counitIso.inv.app _ ≫ U.functor.map (U.unitIso.inv.app M₀ ≫ i) = _
    rw [Functor.map_comp, ← Category.assoc, U.counitInv_functor_comp]
    exact Category.id_comp _
  have hi : adj'.homEquiv (U.functor.obj M₀) L t' = U.functor.map i ≫ e.hom.app L := by
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv,
      Adjunction.comp_homEquiv]
    change U.symm.toAdjunction.homEquiv _ _
      (adj₀.homEquiv _ _ (V.toAdjunction.homEquiv _ _ t')) ≫ e.hom.app L = _
    exact congrArg (fun z ↦ z ≫ e.hom.app L)
      ((congrArg (fun z ↦ U.symm.toAdjunction.homEquiv _ _ (adj₀.homEquiv _ _ z)) hv).trans
        ((congrArg (fun z ↦ U.symm.toAdjunction.homEquiv _ _ z) hq).trans hu))
  let j := U.functor.map i ≫ e.hom.app L
  have he : (adj.homEquiv _ L).symm j =
      (adj.leftAdjointUniq adj').hom.app _ ≫ t' := by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit, hi]
  refine ⟨j, inferInstance, ?_⟩
  rw [he]
  have : IsIso t' := by
    dsimp only [t']
    rw [Adjunction.homEquiv_counit]
    infer_instance
  infer_instance

@[implicit_reducible]
private noncomputable def coefficient_module_equivalence
    {A₀ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A₀] [IsCommMonObj A₀] [MonObj A] [IsCommMonObj A]
    (r : A₀ ≅ A) [IsMonHom r.hom] (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A₀ X) ≌
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X) :=
  CategoryTheory.Equivalence.mk (Mod.comap (coefficientMap r.inv X))
    (Mod.comap (coefficientMap r.hom X))
    ((Mod.comapId _).symm ≪≫ Mod.comapCongr (by
      rw [← coefficientMap_comp, r.hom_inv_id, coefficientMap_id]) ≪≫
        Mod.comapComp (coefficientMap r.hom X) (coefficientMap r.inv X))
    ((Mod.comapComp (coefficientMap r.inv X) (coefficientMap r.hom X)).symm ≪≫
      Mod.comapCongr (by rw [← coefficientMap_comp, r.inv_hom_id, coefficientMap_id]) ≪≫
        Mod.comapId _)

private theorem lattice_coefficient_transport
    (A₀ B₀ A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A₀] [IsCommMonObj A₀] [MonObj B₀] [IsCommMonObj B₀]
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a₀ : A₀ ⟶ B₀) [IsMonHom a₀] (a : A ⟶ B) [IsMonHom a]
    (r : A₀ ≅ A) [IsMonHom r.hom] (s : B₀ ≅ B) [IsMonHom s.hom]
    (w : a₀ ≫ s.hom = r.hom ≫ a) (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A₀ X))
    (hM : IsLisseCoefficientModule A₀ M)
    (ι : M ⟶ (Mod.comap (coefficientMap a₀ X)).obj
      ((Mod.comap (coefficientMap s.hom X)).obj L)) [Mono ι]
    [IsIso (((Mod.extendRestrictAdjunction (coefficientMap a₀ X)).homEquiv M
      ((Mod.comap (coefficientMap s.hom X)).obj L)).symm ι)] :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X),
      IsLisseCoefficientModule A N ∧
      ∃ j : N ⟶ (Mod.comap (coefficientMap a X)).obj L,
        Mono j ∧ IsIso (((Mod.extendRestrictAdjunction
          (coefficientMap a X)).homEquiv N L).symm j) := by
  let U := coefficient_module_equivalence r X
  let V := coefficient_module_equivalence s X
  let : IsIso (((Mod.extendRestrictAdjunction (coefficientMap a₀ X)).homEquiv
      M (V.inverse.obj L)).symm ι) := inferInstanceAs
    (IsIso (((Mod.extendRestrictAdjunction (coefficientMap a₀ X)).homEquiv
      M ((Mod.comap (coefficientMap s.hom X)).obj L)).symm ι))
  obtain ⟨j, hj, ht⟩ := transport_lattice_arrow
    (Mod.extendRestrictAdjunction (coefficientMap a₀ X))
    (Mod.extendRestrictAdjunction (coefficientMap a X)) U V
    (coefficient_square_transport A₀ B₀ A B a₀ a r s w X) L M ι
  exact ⟨U.functor.obj M, lisse_comap r.inv X M hM, j, hj, ht⟩

private theorem lattice_target_iso
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (L L' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (e : L ≅ L')
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X))
    (ι : M ⟶ (Mod.comap (coefficientMap a X)).obj L) [Mono ι]
    [IsIso (((Mod.extendRestrictAdjunction (coefficientMap a X)).homEquiv M L).symm ι)] :
    ∃ j : M ⟶ (Mod.comap (coefficientMap a X)).obj L',
      Mono j ∧ IsIso (((Mod.extendRestrictAdjunction
        (coefficientMap a X)).homEquiv M L').symm j) := by
  let j := ι ≫ (Mod.comap (coefficientMap a X)).map e.hom
  refine ⟨j, inferInstance, ?_⟩
  rw [Adjunction.homEquiv_naturality_right_symm]
  infer_instance

private theorem lattice_pullback
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X))
    (hM : IsLisseCoefficientModule A M)
    (ι : M ⟶ (Mod.comap (coefficientMap a X)).obj L) [Mono ι]
    [IsIso (((Mod.extendRestrictAdjunction (coefficientMap a X)).homEquiv M L).symm ι)] :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj A Y),
      IsLisseCoefficientModule A N ∧
      ∃ j : N ⟶ (Mod.comap (coefficientMap a Y)).obj
          ((CondensedRing.upperStar B f).obj L),
        Mono j ∧ IsIso (((Mod.extendRestrictAdjunction
          (coefficientMap a Y)).homEquiv N ((CondensedRing.upperStar B f).obj L)).symm j) := by
  let F := CondensedRing.upperStar A f
  let G := CondensedRing.upperStar B f
  let adjX := Mod.extendRestrictAdjunction (coefficientMap a X)
  let adjY := Mod.extendRestrictAdjunction (coefficientMap a Y)
  let e := (CondensedRing.comapUpperStarIso a f).symm
  let j := F.map ι ≫ e.hom.app L
  have hN : IsLisseCoefficientModule A (F.obj M) :=
    (lisse_iff_locallyFree A _).mpr
      (CondensedRing.locallyFree_upperStar A f ((lisse_iff_locallyFree A M).mp hM))
  refine ⟨F.obj M, hN, j, inferInstance, ?_⟩
  let t := (adjX.homEquiv M L).symm ι
  have ht : adjX.homEquiv M L t = ι := (adjX.homEquiv M L).apply_symm_apply ι
  have hj : (adjY.homEquiv (F.obj M) (G.obj L)).symm j =
      (CondensedRing.pullIso a f).hom.app M ≫ G.map t := by
    apply (adjY.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    rw [Functor.map_comp, ← Category.assoc]
    rw [← ordinaryScalarUnit a f M]
    have hn := e.hom.naturality t
    dsimp only [Functor.comp_map, e, Iso.symm_hom, G] at hn
    rw [Category.assoc, ← hn, ← Category.assoc, ← F.map_comp]
    have ht' := ht
    rw [Adjunction.homEquiv_unit] at ht'
    rw [ht']
    rfl
  rw [hj]
  infer_instance

/-- Realize an ordered refinement with actual maps into the original strata. -/
private theorem exists_ordered_factorizing_refinement
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)] (S : Scheme.{u}) [IsNoetherian S]
    (P : S.FiniteLocallyClosedStratification) :
    ∃ R : S.FiniteLocallyClosedStratification,
      (∀ b : Fin (R.n + 1),
        IsOpen (⋃ i : Fin R.n, ⋃ (_ : i.val < b.val), R.stratum i)) ∧
      ∃ (a : Fin R.n → Fin P.n)
        (f : ∀ b, R.domain b ⟶ P.domain (a b)),
        ∀ b, f b ≫ P.immersion (a b) = R.immersion b := by
  classical
  obtain ⟨Q, hQ, _, ho⟩ :=
    coefficientHeart_commonStratification_refinement Λ S 1 (fun _ ↦ P)
  choose a ha using hQ 0
  have hP (b : Fin P.n) : IsImmersion (P.immersion b) := P.isImmersion b
  have hQi (b : Fin Q.n) : IsImmersion (Q.immersion b) := Q.isImmersion b
  let R : S.FiniteLocallyClosedStratification := {
    toFiniteLocallyClosedStratification := Q.toFiniteLocallyClosedStratification
    domain := fun b ↦ pullback (P.immersion (a b)) (Q.immersion b)
    immersion := fun b ↦ pullback.snd _ _ ≫ Q.immersion b
    isImmersion := fun b ↦ inferInstance
    range_immersion := fun b ↦ by
      rw [Scheme.Pullback.range_snd_comp, P.range_immersion, Q.range_immersion]
      exact Set.inter_eq_right.mpr (ha b) }
  exact ⟨R, ho, a, fun b ↦ pullback.fst _ _, fun b ↦ pullback.condition⟩

/-- The data of a lattice, keeping the dependent module objects behind projections. -/
private structure LisseLattice
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X)) where
  model : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X)
  lisse : IsLisseCoefficientModule A model
  inclusion : model ⟶ (Mod.comap (coefficientMap c X)).obj L
  mono : Mono inclusion
  scalarIso : IsIso (((Mod.extendRestrictAdjunction
    (coefficientMap c X)).homEquiv model L).symm inclusion)

private theorem transport_stratified_lattices
    (A₀ B₀ A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A₀] [IsCommMonObj A₀] [MonObj B₀] [IsCommMonObj B₀]
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a₀ : A₀ ⟶ B₀) [IsMonHom a₀] (c : A ⟶ B) [IsMonHom c]
    (r : A₀ ≅ A) [IsMonHom r.hom] (s : B₀ ≅ B) [IsMonHom s.hom]
    (w : a₀ ≫ s.hom = r.hom ≫ c) (S : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj B S))
    (P : S.FiniteLocallyClosedStratification)
    (hP : ∀ b : Fin P.n,
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology (P.domain b)) Ab.{u + 1})
          (condensedRingObj A₀ (P.domain b)),
        CondensedRing.LocallyFree (condensedRingObj A₀ (P.domain b)) M ∧
        ∃ ι : M ⟶ (Mod.comap (coefficientMap a₀ (P.domain b))).obj
            ((CondensedRing.upperStar B₀ (P.immersion b)).obj
              ((Mod.comap (coefficientMap s.hom S)).obj L)),
          Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
            (coefficientMap a₀ (P.domain b))).homEquiv M
              ((CondensedRing.upperStar B₀ (P.immersion b)).obj
                ((Mod.comap (coefficientMap s.hom S)).obj L))).symm ι)) :
    Nonempty (∀ b : Fin P.n, LisseLattice A B c (P.domain b)
      ((CondensedRing.upperStar B (P.immersion b)).obj L)) := by
  classical
  have h (b : Fin P.n) : Nonempty (LisseLattice A B c (P.domain b)
      ((CondensedRing.upperStar B (P.immersion b)).obj L)) := by
    obtain ⟨M, hM, ι, hι, ht⟩ := hP b
    let : Mono ι := hι
    let : IsIso (((Mod.extendRestrictAdjunction (coefficientMap a₀ (P.domain b))).homEquiv
        M ((CondensedRing.upperStar B₀ (P.immersion b)).obj
          ((Mod.comap (coefficientMap s.hom S)).obj L))).symm ι) := ht
    let z := (CondensedRing.comapUpperStarIso s.hom (P.immersion b)).symm.app L
    obtain ⟨ι', hι', ht'⟩ := lattice_target_iso A₀ B₀ a₀ (P.domain b)
      ((CondensedRing.upperStar B₀ (P.immersion b)).obj
        ((Mod.comap (coefficientMap s.hom S)).obj L)) _ z M ι
    let : Mono ι' := hι'
    let : IsIso (((Mod.extendRestrictAdjunction (coefficientMap a₀ (P.domain b))).homEquiv
        M ((Mod.comap (coefficientMap s.hom (P.domain b))).obj
          ((CondensedRing.upperStar B (P.immersion b)).obj L))).symm ι') := ht'
    obtain ⟨N, hN, j, hj, hu⟩ := lattice_coefficient_transport A₀ B₀ A B a₀ c r s w
      (P.domain b) ((CondensedRing.upperStar B (P.immersion b)).obj L) M
      ((lisse_iff_locallyFree A₀ M).mpr hM) ι'
    exact ⟨⟨N, hN, j, hj, hu⟩⟩
  exact ⟨fun b ↦ (h b).some⟩

private theorem ordered_refinement_lattices
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B]
    (c : coefficientHeartRingObj Λ ⟶ B) [IsMonHom c]
    (S : Scheme.{u}) [IsNoetherian S]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj B S))
    (P : S.FiniteLocallyClosedStratification)
    (lat : ∀ b : Fin P.n, LisseLattice (coefficientHeartRingObj Λ) B c (P.domain b)
      ((CondensedRing.upperStar B (P.immersion b)).obj L)) :
    ∃ R : S.FiniteLocallyClosedStratification,
      (∀ b : Fin (R.n + 1), IsOpen (⋃ i : Fin R.n, ⋃ (_ : i.val < b.val), R.stratum i)) ∧
      ∃ M : ∀ b : Fin R.n, Mod (Sheaf (Scheme.ProEt.topology (R.domain b)) Ab.{u + 1})
          (condensedRingObj (coefficientHeartRingObj Λ) (R.domain b)),
        ∀ b : Fin R.n, IsLisseCoefficientModule (coefficientHeartRingObj Λ) (M b) ∧
          ∃ ι : M b ⟶ (Mod.comap (coefficientMap c (R.domain b))).obj
              ((CondensedRing.upperStar B (R.immersion b)).obj L),
            Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
              (coefficientMap c (R.domain b))).homEquiv (M b)
                ((CondensedRing.upperStar B (R.immersion b)).obj L)).symm ι) := by
  classical
  let A := coefficientHeartRingObj Λ
  obtain ⟨R, ho, a, f, hf⟩ := exists_ordered_factorizing_refinement Λ S P
  have hb (b : Fin R.n) : Nonempty (LisseLattice A B c (R.domain b)
      ((CondensedRing.upperStar B (R.immersion b)).obj L)) := by
    let M := lat (a b)
    let : Mono M.inclusion := M.mono
    let : IsIso (((Mod.extendRestrictAdjunction (coefficientMap c (P.domain (a b)))).homEquiv
        M.model ((CondensedRing.upperStar B (P.immersion (a b))).obj L)).symm M.inclusion) :=
      M.scalarIso
    obtain ⟨N, hN, j, hj, hu⟩ := lattice_pullback A B c (f b)
      ((CondensedRing.upperStar B (P.immersion (a b))).obj L) M.model M.lisse M.inclusion
    let : Mono j := hj
    let : IsIso (((Mod.extendRestrictAdjunction (coefficientMap c (R.domain b))).homEquiv
        N ((CondensedRing.upperStar B (f b)).obj
          ((CondensedRing.upperStar B (P.immersion (a b))).obj L))).symm j) := hu
    let z := ((CondensedRing.upperStarComp B (f b) (P.immersion (a b))).symm.app L) ≪≫
      eqToIso (congrArg (fun g ↦ (CondensedRing.upperStar B g).obj L) (hf b))
    obtain ⟨j', hj', hu'⟩ := lattice_target_iso A B c (R.domain b)
      ((CondensedRing.upperStar B (f b)).obj
        ((CondensedRing.upperStar B (P.immersion (a b))).obj L)) _ z N j
    exact ⟨⟨N, hN, j', hj', hu'⟩⟩
  let N := fun b ↦ (hb b).some
  refine ⟨R, ho, fun b ↦ (N b).model, fun b ↦ ?_⟩
  exact ⟨(N b).lisse, (N b).inclusion, (N b).mono, (N b).scalarIso⟩

private def OrderedLatticeProperty
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c] (S : Scheme.{u}) : Prop :=
  ∀ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj B S),
    IsLisseCoefficientModule B L →
    ∃ R : S.FiniteLocallyClosedStratification,
      (∀ b : Fin (R.n + 1), IsOpen (⋃ i : Fin R.n, ⋃ (_ : i.val < b.val), R.stratum i)) ∧
      ∃ M : ∀ b : Fin R.n, Mod (Sheaf (Scheme.ProEt.topology (R.domain b)) Ab.{u + 1})
          (condensedRingObj A (R.domain b)),
        ∀ b : Fin R.n, IsLisseCoefficientModule A (M b) ∧
          ∃ ι : M b ⟶ (Mod.comap (coefficientMap c (R.domain b))).obj
              ((CondensedRing.upperStar B (R.immersion b)).obj L),
            Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
              (coefficientMap c (R.domain b))).homEquiv (M b)
                ((CondensedRing.upperStar B (R.immersion b)).obj L)).symm ι)

private theorem ordered_lattice_unpack
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c] (S : Scheme.{u})
    (h : OrderedLatticeProperty A B c S) :
  ∀ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj B S),
    IsLisseCoefficientModule B L →
    ∃ R : S.FiniteLocallyClosedStratification,
      (∀ b : Fin (R.n + 1), IsOpen (⋃ i : Fin R.n, ⋃ (_ : i.val < b.val), R.stratum i)) ∧
      ∃ M : ∀ b : Fin R.n, Mod (Sheaf (Scheme.ProEt.topology (R.domain b)) Ab.{u + 1})
          (condensedRingObj A (R.domain b)),
        ∀ b : Fin R.n, IsLisseCoefficientModule A (M b) ∧
          ∃ ι : M b ⟶ (Mod.comap (coefficientMap c (R.domain b))).obj
              ((CondensedRing.upperStar B (R.immersion b)).obj L),
            Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
              (coefficientMap c (R.domain b))).homEquiv (M b)
                ((CondensedRing.upperStar B (R.immersion b)).obj L)).symm ι) := h

private def RawStratifiedLattices
    (A₀ B₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A₀] [IsCommMonObj A₀] [MonObj B₀] [IsCommMonObj B₀]
    (a₀ : A₀ ⟶ B₀) [IsMonHom a₀] (S : Scheme.{u}) : Prop :=
  ∀ L₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj B₀ S),
      CondensedRing.LocallyFree (condensedRingObj B₀ S) L₀ →
      ∃ P : S.FiniteLocallyClosedStratification, ∀ b : Fin P.n,
        ∃ M : Mod (Sheaf (Scheme.ProEt.topology (P.domain b)) Ab.{u + 1})
            (condensedRingObj A₀ (P.domain b)),
          CondensedRing.LocallyFree (condensedRingObj A₀ (P.domain b)) M ∧
          ∃ ι : M ⟶ (Mod.comap (coefficientMap a₀ (P.domain b))).obj
              ((CondensedRing.upperStar B₀ (P.immersion b)).obj L₀),
            Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
              (coefficientMap a₀ (P.domain b))).homEquiv M
                ((CondensedRing.upperStar B₀ (P.immersion b)).obj L₀)).symm ι)

-- Instance search for the spectral norm must find the same `IsLocalRing`/`IsDomain` proofs as in
-- `StratifiedLattice`; otherwise the kernel unfolds the coefficient topology and times out.
attribute [-instance] IsRegularLocalRing.toIsLocalRing HenselianLocalRing.toIsLocalRing
  IsDomain.of_isSimpleRing in
private theorem small_spectral_raw_lattices
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type) [Field K] [Algebra ℚ_[ℓ] K]
    [FiniteDimensional ℚ_[ℓ] K] (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p] (hpℓ : p ≠ ℓ)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))] :
    letI := spectralNorm.nontriviallyNormedField ℚ_[ℓ] K
    let A₀ := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers ℓ K)
    let B₀ := Profinite.continuousMapRingObj.{u} K
    let a₀ : A₀ ⟶ B₀ := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap
          (Padic.coefficientExtensionIntegers ℓ K).subtype continuous_subtype_val)
    RawStratifiedLattices A₀ B₀ a₀ S :=
  CondensedRing.exists_stratified_lisse_integral_lattice ℓ K p k hpℓ S

private theorem ordered_lattices_of_coefficient_square
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (A₀ B₀ B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A₀] [IsCommMonObj A₀] [MonObj B₀] [IsCommMonObj B₀]
    [MonObj B] [IsCommMonObj B]
    (a₀ : A₀ ⟶ B₀) [IsMonHom a₀]
    (c : coefficientHeartRingObj Λ ⟶ B) [IsMonHom c]
    (r : A₀ ≅ coefficientHeartRingObj Λ) [IsMonHom r.hom]
    (s : B₀ ≅ B) [IsMonHom s.hom] (w : a₀ ≫ s.hom = r.hom ≫ c)
    (S : Scheme.{u}) [IsNoetherian S]
    (hsmall : RawStratifiedLattices A₀ B₀ a₀ S) :
    OrderedLatticeProperty (coefficientHeartRingObj Λ) B c S := by
  intro L hL
  let L₀ := (Mod.comap (coefficientMap s.hom S)).obj L
  have hL₀ : CondensedRing.LocallyFree (condensedRingObj B₀ S) L₀ :=
    (lisse_iff_locallyFree B₀ _).mp (lisse_comap s.hom S L hL)
  obtain ⟨P, hP⟩ := hsmall L₀ hL₀
  obtain ⟨lat⟩ := transport_stratified_lattices A₀ B₀ (coefficientHeartRingObj Λ) B
    a₀ c r s w S L P hP
  exact ordered_refinement_lattices Λ B c S L P lat

attribute [local irreducible] CondensedRing.upperStar Mod.extendRestrictAdjunction
  Mod.comap Padic.coefficientExtensionIntegers

/-- A lisse spectral-coefficient module has integral lattices on strata with open prefixes. -/
theorem exists_orderedSpectralLattices (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (_hpℓ : p ≠ ℓ)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] :
  letI := spectralNorm.nontriviallyNormedField ℚ_[ℓ] E
  let A := coefficientHeartRingObj (Profinite.continuousMapRingSheafOfUniverse.{u, u}
    (Padic.coefficientExtensionIntegers ℓ E))
  letI : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers ℓ E))
      (fun U (a b : ULift.{u + 1} C(U.unop, Padic.coefficientExtensionIntegers ℓ E)) ↦
        mul_comm a b)
  let B := coefficientHeartRingObj (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
  letI : IsCommMonObj B := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
      (fun U (a b : ULift.{u + 1} C(U.unop, E)) ↦ mul_comm a b)
  let c := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val)
  ∀ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj B S),
    IsLisseCoefficientModule B L →
    ∃ R : S.FiniteLocallyClosedStratification,
      (∀ b : Fin (R.n + 1),
        IsOpen (⋃ i : Fin R.n, ⋃ (_ : i.val < b.val), R.stratum i)) ∧
      ∃ M : ∀ b : Fin R.n,
        Mod (Sheaf (Scheme.ProEt.topology (R.domain b)) Ab.{u + 1})
          (condensedRingObj A (R.domain b)),
        ∀ b : Fin R.n, IsLisseCoefficientModule A (M b) ∧
          ∃ ι : M b ⟶ (Mod.comap ((upperStarFromPoint (R.domain b)).map c)).obj
              ((CondensedRing.upperStar B (R.immersion b)).obj L),
            Mono ι ∧ IsIso
              (((Mod.extendRestrictAdjunction ((upperStarFromPoint (R.domain b)).map c)).homEquiv
                (M b) ((CondensedRing.upperStar B (R.immersion b)).obj L)).symm ι) := by
  classical
  let fE : Field E := inferInstance
  let aE : Algebra ℚ_[ℓ] E := inferInstance
  let := spectralNorm.nontriviallyNormedField ℚ_[ℓ] E
  let : Field E := fE
  let : Algebra ℚ_[ℓ] E := aE
  intro A B c
  let : IsMonHom c := Sheaf.isMonHom_sheafCompose_map _
    (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val)
  let : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers ℓ E))
    (fun U (a b : ULift.{u + 1} C(U.unop, Padic.coefficientExtensionIntegers ℓ E)) ↦
      mul_comm a b)
  let : IsCommMonObj B := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
    (fun U (a b : ULift.{u + 1} C(U.unop, E)) ↦ mul_comm a b)
  let OA := Profinite.continuousMapRingSheafOfUniverse.{u, u}
    (Padic.coefficientExtensionIntegers ℓ E)
  let model := smallAlgebraModel ℓ E
  let K := model.carrier
  let : Field K := model.field
  let : Algebra ℚ_[ℓ] K := model.algebra
  let : FiniteDimensional ℚ_[ℓ] K := model.finite
  let e : K ≃ₐ[ℚ_[ℓ]] E := model.equiv
  let fK : Field K := inferInstance
  let aK : Algebra ℚ_[ℓ] K := inferInstance
  let := spectralNorm.nontriviallyNormedField ℚ_[ℓ] K
  let : Field K := fK
  let : Algebra ℚ_[ℓ] K := aK
  let square := spectralCoefficientSquare ℓ e
  let rRing := square.integral
  let sRing := square.rational
  let H := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let A₀ := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers ℓ K)
  let B₀ := Profinite.continuousMapRingObj.{u} K
  let a₀ : A₀ ⟶ B₀ := H.map
    (Profinite.continuousMapRingSheafMap
      (Padic.coefficientExtensionIntegers ℓ K).subtype continuous_subtype_val)
  let : IsMonHom a₀ := Sheaf.isMonHom_sheafCompose_map _
    (Profinite.continuousMapRingSheafMap
      (Padic.coefficientExtensionIntegers ℓ K).subtype continuous_subtype_val)
  let r : A₀ ≅ A := H.mapIso rRing
  let s : B₀ ≅ B := H.mapIso sRing
  have : IsMonHom r.hom := Sheaf.isMonHom_sheafCompose_map _ rRing.hom
  have : IsMonHom s.hom := Sheaf.isMonHom_sheafCompose_map _ sRing.hom
  have w : a₀ ≫ s.hom = r.hom ≫ c := by
    change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
    rw [← H.map_comp, ← H.map_comp]
    exact congrArg H.map square.commutes
  have : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of k))
  have : CompactSpace S :=
    QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
  have : IsNoetherian S := ⟨⟩
  have h : OrderedLatticeProperty A B c S :=
    ordered_lattices_of_coefficient_square OA A₀ B₀ B a₀ c r s w S
      (small_spectral_raw_lattices ℓ K p k _hpℓ S)
  exact ordered_lattice_unpack A B c S h

end AlgebraicGeometry.ProEtale
