/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.CategoryTheory.AdicSites.Morphism.CompletionMateComparison

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
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all WeilConjectures.AlgebraicGeometry.StrictTower.ConstantNormalization.ConstantTowerDirectImageNormalization
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.Right.RightFractionDenseSubcategory
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
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
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
/-! # Models for constant-coefficient strict reduction on the original pro-etale site

This is the original-site specialization of the existing strict quotient-tower construction.
The site retains object universe t+1 and morphism universe t.

## References

* Stacks Tags 099M, 099N and 0E48
* Stacks 0941
* Stacks 06YY and 0D6D
* Stacks 03EL and 06YY
* Stacks 0B56, 099M
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange
attribute [local irreducible] completedAdicChangeData

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The quotient maps commute with canonical inverse image of the coefficients. -/
theorem quotient_comm {U V : Scheme.{t}} (f : U ⟶ V) (n : ℕ) :
    (exchangeConstantIso.{t} f A).hom ≫
        (exchangeScalar.{t} d U ≫ AdicCoefficientDatum.projection.{t} d U n) =
      (proEtaleSheafInverseImage.{t, t + 2} f CommRingCat.{t + 1}).map
        (exchangeScalar.{t} d V ≫ AdicCoefficientDatum.projection.{t} d V n) ≫
          (AdicCoefficientDatum.finiteRingIso.{t} d f n).hom := by
  rw [← Category.assoc, exchangeScalar_comm, Category.assoc, d.projection_comm]
  rw [← Category.assoc, ← Functor.map_comp]

/-- The existing ambient constant-coefficient derived category. -/
abbrev D (T : Scheme.{t}) := reductionDerivedCategory T (exchangeConstantRing T A)

/-- The existing derived category of strict constant-coefficient towers. -/
abbrev TD (T : Scheme.{t}) := DerivedCategory (exchangeTowers T (exchangeConstantRing T A))

/-- The quotient map from constant coefficients to the given finite coefficient sheaf. -/
def quotient (T : Scheme.{t}) (n : ℕ) :
    exchangeConstantRing T A ⟶ d.finiteRing T n := exchangeScalar d T ≫ d.projection T n

/-- Ordinary tensor with the quotient, retaining the original constant scalar action. -/
def level (T : Scheme.{t}) (n : ℕ) :
    reductionModules T (exchangeConstantRing T A) ⥤
      reductionModules T (exchangeConstantRing T A) :=
  reductionChange T (quotient d T n) ⋙ reductionRestrict T (quotient d T n)

section CompactQuotient

open scoped ChangeOfRings
open AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization

set_option backward.isDefEq.respectTransparency false in
private abbrev levelUnitMap (X : Scheme.{t}) (n : ℕ)
    (M : reductionModules X (exchangeConstantRing X A)) : M ⟶ (level d X n).obj M :=
  (pbcScalarAdjunction (quotient d X n)).unit.app M

set_option backward.isDefEq.respectTransparency false in
private theorem levelUnitMap_apply (X : Scheme.{t}) (n : ℕ)
    (M : reductionModules X (exchangeConstantRing X A))
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    (levelUnitMap d X n M).val.app U x =
      reductionTensorSection X (quotient d X n) M U 1 x := by
  unfold levelUnitMap pbcScalarAdjunction
  exact (pbcScalarAdjunction_exists (quotient d X n)).exists.choose_spec M U x

open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorSection_map (X : Scheme.{t}) (n : ℕ)
    {M N : reductionModules X (exchangeConstantRing X A)} (a : M ⟶ N) (U : X.ProEtᵒᵖ)
    (s : (d.finiteRing X n).obj.obj U) (x : M.val.obj U) :
    ((level d X n).map a).val.app U
        (reductionTensorSection X (quotient d X n) M U s x) =
      reductionTensorSection X (quotient d X n) N U s (a.val.app U x) := by
  let φ := quotient d X n
  have hu := (pbcScalarAdjunction_exists φ).exists.choose_spec
  have hn := congrArg (fun k ↦ k.val.app U x) ((pbcScalarAdjunction φ).unit.naturality a)
  change ((pbcScalarAdjunction φ).unit.app N).val.app U (a.val.app U x) =
    ((reductionChange X φ).map a).val.app U
      (((pbcScalarAdjunction φ).unit.app M).val.app U x) at hn
  unfold pbcScalarAdjunction at hn
  erw [hu, hu] at hn
  have hM := tensorSection_smul X φ M U s 1 x
  have hN := tensorSection_smul X φ N U s 1 (a.val.app U x)
  rw [mul_one] at hM hN
  change ((reductionChange X φ).map a).val.app U
    (reductionTensorSection X φ M U s x) = _
  erw [← hM, map_smul, ← hn, hN]
set_option backward.isDefEq.respectTransparency false in
private theorem quotientStep_comp (T : Scheme.{t}) (n : ℕ) :
    quotient d T (n + 1) ≫ reductionCoefficientMap T d (n + 1) n (Nat.le_succ n) =
      quotient d T n := by
  unfold quotient AdicCoefficientDatum.projection
  rw [Category.assoc, completedReductionProjection_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The strict quotient transition is determined on sheafified pure tensors. -/
theorem step_existsUnique (T : Scheme.{t}) (n : ℕ) :
    ∃! τ : level d T (n + 1) ⟶ level d T n,
      ∀ (M : reductionModules T (exchangeConstantRing T A)) (U : T.ProEtᵒᵖ)
        (s : (d.finiteRing T (n + 1)).obj.obj U) (x : M.val.obj U),
        (τ.app M).val.app U (reductionTensorSection T (quotient d T (n + 1)) M U s x) =
          reductionTensorSection T (quotient d T n) M U
            ((reductionCoefficientMap T d (n + 1) n (Nat.le_succ n)).hom.app U s) x := by
  let b (M : reductionModules T (exchangeConstantRing T A)) :=
    (step_map_exists T (quotient d T (n + 1)) (quotient d T n)
      (reductionCoefficientMap T d (n + 1) n (Nat.le_succ n))
      (quotientStep_comp d T n) M (levelUnitMap d T n M)
      (levelUnitMap_apply d T n M)).choose
  have hb (M : reductionModules T (exchangeConstantRing T A)) :=
    (step_map_exists T (quotient d T (n + 1)) (quotient d T n)
      (reductionCoefficientMap T d (n + 1) n (Nat.le_succ n))
      (quotientStep_comp d T n) M (levelUnitMap d T n M)
      (levelUnitMap_apply d T n M)).choose_spec
  let τ : level d T (n + 1) ⟶ level d T n :=
    { app := b
      naturality := by
        intro M N f
        apply level_hom_ext T (quotient d T (n + 1)) M ((level d T n).obj N)
        intro U s x
        change (b N).val.app U (((level d T (n + 1)).map f).val.app U
            (reductionTensorSection T (quotient d T (n + 1)) M U s x)) =
          ((level d T n).map f).val.app U ((b M).val.app U
            (reductionTensorSection T (quotient d T (n + 1)) M U s x))
        rw [tensorSection_map, hb, hb, tensorSection_map] }
  refine ⟨τ, ?_, ?_⟩
  · intro M U s x
    exact hb M U s x
  · intro τ' hτ'
    apply NatTrans.ext
    funext M
    apply level_hom_ext T (quotient d T (n + 1)) M ((level d T n).obj M)
    intro U s x
    exact (hτ' M U s x).trans (hb M U s x).symm

/-- The actual quotient transition, with its tensor formula retained. -/
def step (T : Scheme.{t}) (n : ℕ) : level d T (n + 1) ⟶ level d T n :=
  (step_existsUnique d T n).exists.choose

/-- The single strict quotient diagram, functorial on ordinary modules. -/
def reductionModule (T : Scheme.{t}) :
    reductionModules T (exchangeConstantRing T A) ⥤
      exchangeTowers T (exchangeConstantRing T A) := (Functor.ofOpSequence (step d T)).flip

/-- Tensor and restriction are additive at every level of this strict diagram. -/
@[instance]
theorem reductionModule_additive (T : Scheme.{t}) : (reductionModule d T).Additive := by
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  have : (level d T n.unop).Additive := by
    dsimp [level]
    infer_instance
  exact (level d T n.unop).map_add

/-- The homotopy functor of the actual strict quotient construction. -/
def reductionHomotopy (T : Scheme.{t}) :=
  (reductionModule d T).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

section CompactReduction
attribute [local irreducible] reductionHomotopy
attribute [local irreducible] completedAdicChange

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalarChangeQuasiIso (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    {P Q : CochainComplex (reductionModules T R) ℤ} (f : P ⟶ Q)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q) (hf : QuasiIso f) :
    QuasiIso (((reductionChange T φ).mapHomologicalComplex (.up ℤ)).map f) := by
  unfold reductionChange completedAdicChange
  exact (completedAdicChangeData T φ).choose_spec.choose_spec.choose_spec.choose_spec.1
    f hP hQ hf

set_option backward.isDefEq.respectTransparency false in
private theorem leftDerivedModels
    {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (E : B ⥤ C) [E.Additive] (P : CochainComplex B ℤ → Prop)
    (res : ∀ K : CochainComplex B ℤ, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K),
      P L ∧ QuasiIso s)
    (inverts : ∀ {K L : CochainComplex B ℤ} (s : K ⟶ L),
      P K → P L → QuasiIso s → QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map s)) :
    Nonempty (DerivedReductionModelData E P) := by
  let H := HomotopyCategory.quotient B (.up ℤ)
  let F := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let S : Set (HomotopyCategory B (.up ℤ)) :=
    { K | ∃ L : CochainComplex B ℤ, P L ∧ H.obj L = K }
  have hres (K : HomotopyCategory B (.up ℤ)) :
      ∃ (K' : HomotopyCategory B (.up ℤ)) (s : K' ⟶ K),
        K' ∈ S ∧ HomotopyCategory.quasiIso B (.up ℤ) s := by
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    obtain ⟨L, s, hL, hs⟩ := res K
    exact ⟨H.obj L, H.map s, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinv (K K' : HomotopyCategory B (.up ℤ)) (s : K ⟶ K')
      (hK : K ∈ S) (hK' : K' ∈ S) (hs : HomotopyCategory.quasiIso B (.up ℤ) s) :
      IsIso (F.map s) := by
    obtain ⟨L, hL, rfl⟩ := hK
    obtain ⟨L', hL', rfl⟩ := hK'
    obtain ⟨a, rfl⟩ := H.map_surjective s
    have ha := (HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 hs
    have hmap := inverts a hL hL' ha
    dsimp only [F, Functor.comp_map, Functor.mapHomotopyCategory_map]
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hmap
  let : F.CommShift ℤ := by dsimp [F]; infer_instance
  have : F.IsTriangulated := by dsimp [F]; infer_instance
  obtain ⟨_, LF, ε, hLF, _, hε⟩ :=
    Functor.leftDerived_from_resolvingClass B (DerivedCategory C) F S hres hinv
  exact ⟨⟨LF, ε, hLF, fun K hK ↦ hε (H.obj K) ⟨K, hK, rfl⟩⟩⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The reduction functor is specified by its universal derived counit and K-flat models. -/
theorem reductionData_exists (T : Scheme.{t}) :
    Nonempty (DerivedReductionModelData (reductionModule d T)
      (CochainComplex.IsKFlatIndependentCoefficients
        (R := exchangeConstantRing T A))) := by
  apply leftDerivedModels (reductionModule d T)
    (CochainComplex.IsKFlatIndependentCoefficients (R := exchangeConstantRing T A))
  · intro K
    obtain ⟨L, s, hL, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
    exact ⟨L, s, hL, hs⟩
  · intro K L s hK hL hs
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro n
    let φ := quotient d T n.unop
    have hchange := scalarChangeQuasiIso T φ s hK hL hs
    change QuasiIso (((reductionRestrict T φ).mapHomologicalComplex (.up ℤ)).map
      (((reductionChange T φ).mapHomologicalComplex (.up ℤ)).map s))
    infer_instance

/-- The chosen universal reduction pair and its computation law. -/
def reductionData (T : Scheme.{t}) :
    DerivedReductionModelData (reductionModule d T)
      (CochainComplex.IsKFlatIndependentCoefficients
        (R := exchangeConstantRing T A)) :=
  Classical.choice (reductionData_exists d T)

/-- The original existential interface, recovered from the universal model data. -/
theorem reduction_exists (T : Scheme.{t}) :
    ∃ (R : D (A := A) T ⥤ TD (A := A) T)
      (ε : DerivedCategory.Qh ⋙ R ⟶ reductionHomotopy d T),
      R.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (reductionModules T (exchangeConstantRing T A)) (.up ℤ)) ∧
      ∀ P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
          (R := exchangeConstantRing T A) P →
        IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  let D := reductionData d T
  unfold reductionHomotopy
  exact ⟨D.reduction, D.counit, D.isLeftDerived, D.isIso_counit⟩

end CompactReduction

/-- The canonical total left derived strict reduction, chosen with its universal counit. -/
def reduction (T : Scheme.{t}) : D (A := A) T ⥤ TD (A := A) T :=
  (reductionData d T).reduction

/-- The universal counit retained in the construction of reduction. -/
def reductionCounit (T : Scheme.{t}) :
    DerivedCategory.Qh ⋙ reduction d T ⟶ reductionHomotopy d T :=
  (reductionData d T).counit

/-- The reduction counit at an actual cochain complex. -/
def reductionComplexCounit (T : Scheme.{t})
    (P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ) :
    (reduction d T).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((reductionModule d T).mapHomologicalComplex (.up ℤ)).obj P) :=
  (reductionData d T).complexCounit P

/-- The existing total right derived inverse limit on strict constant towers. -/
abbrev rlim (T : Scheme.{t}) := completedRlim T (exchangeConstantRing T A)

/-- Constant-coefficient quotient-tower completion. -/
def completion (T : Scheme.{t}) : D (A := A) T ⥤ D (A := A) T := reduction d T ⋙ rlim (A := A) T

/-- The exact constant-diagram functor on the ambient derived category. -/
abbrev diagonal (T : Scheme.{t}) :=
  (Functor.const ℕᵒᵖ : reductionModules T (exchangeConstantRing T A) ⥤
    exchangeTowers T (exchangeConstantRing T A)).mapDerivedCategory

/-- The constant diagram/derived limit adjunction, with its ordinary unit. -/
def diagonalAdjunction (T : Scheme.{t}) : diagonal (A := A) T ⊣ rlim (A := A) T :=
  (constLimAdj : (Functor.const ℕᵒᵖ) ⊣
    completedTowerLimit T (exchangeConstantRing T A)).mapDerivedCategoryRightDerivedAdjunction

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary quotient augmentation is fixed on every section by x maps to 1 tensor x. -/
theorem ordinaryAugmentation_existsUnique (T : Scheme.{t}) :
    ∃! η : (Functor.const ℕᵒᵖ : reductionModules T (exchangeConstantRing T A) ⥤
        exchangeTowers T (exchangeConstantRing T A)) ⟶ reductionModule d T,
      ∀ (M : reductionModules T (exchangeConstantRing T A)) (n : ℕ) (U : T.ProEtᵒᵖ)
        (x : M.val.obj U),
        ((η.app M).app (op n)).val.app U x =
          reductionTensorSection T (quotient d T n) M U 1 x := by
  let η : (Functor.const ℕᵒᵖ : reductionModules T (exchangeConstantRing T A) ⥤
      exchangeTowers T (exchangeConstantRing T A)) ⟶ reductionModule d T :=
    { app := fun M ↦ NatTrans.ofOpSequence (fun n ↦ levelUnitMap d T n M) (by
        intro n
        change levelUnitMap d T n M = levelUnitMap d T (n + 1) M ≫
          ((Functor.ofOpSequence (step d T)).map
            (homOfLE (n.le_add_right 1)).op).app M
        rw [Functor.ofOpSequence_map_homOfLE_succ]
        ext U x
        change (levelUnitMap d T n M).val.app U x =
          (((step_existsUnique d T n).exists.choose).app M).val.app U
            ((levelUnitMap d T (n + 1) M).val.app U x)
        rw [levelUnitMap_apply, levelUnitMap_apply,
          (step_existsUnique d T n).exists.choose_spec]
        simp only [map_one])
      naturality := by
        intro M N a
        apply NatTrans.ext
        funext n
        ext U x
        change (levelUnitMap d T n.unop N).val.app U (a.val.app U x) =
          ((level d T n.unop).map a).val.app U
            ((levelUnitMap d T n.unop M).val.app U x)
        rw [levelUnitMap_apply, levelUnitMap_apply, tensorSection_map] }
  refine ⟨η, ?_, ?_⟩
  · intro M n U x
    exact levelUnitMap_apply d T n M U x
  · intro η' hη'
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    ext U x
    exact (hη' M n.unop U x).trans (levelUnitMap_apply d T n.unop M U x).symm

/-- The ordinary augmentation with its sectionwise normalization. -/
def ordinaryAugmentation (T : Scheme.{t}) :
    (Functor.const ℕᵒᵖ : reductionModules T (exchangeConstantRing T A) ⥤
      exchangeTowers T (exchangeConstantRing T A)) ⟶ reductionModule d T :=
  (ordinaryAugmentation_existsUnique d T).exists.choose

set_option backward.isDefEq.respectTransparency false in
private theorem lift_complex_fac
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (E F : B ⥤ C) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [F.Additive] (L : DerivedCategory B ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (τ : E ⟶ F) (η : E.mapDerivedCategory ⟶ L)
    (hη : ∀ K, η.app (DerivedCategory.Qh.obj K) ≫ ε.app K =
      E.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app K))
    (P : CochainComplex B ℤ) :
    η.app (DerivedCategory.Q.obj P) ≫
        AlgebraicGeometry.Scheme.reductionComplexCounit F L ε P =
      E.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app P) := by
  dsimp only [AlgebraicGeometry.Scheme.reductionComplexCounit]
  rw [← η.naturality_assoc, ← Category.assoc (η.app _)]
  erw [hη ((HomotopyCategory.quotient B (.up ℤ)).obj P)]
  rw [E.mapDerivedCategoryFactorsh_hom_app]
  have hτ : DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app
        ((HomotopyCategory.quotient B (.up ℤ)).obj P)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app P) := rfl
  have hF : (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P =
      𝟙 ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) := rfl
  simp only [AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.quotient_inv_id,
    AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.quotient_hom_id,
    AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.homotopyFactors_inv_id, hF,
    Category.assoc, hτ]
  erw [E.mapDerivedCategory.map_id, (DerivedCategory.Qh (C := C)).map_id,
    (DerivedCategory.Qh (C := C)).map_id]
  erw [Category.id_comp, Category.id_comp, Category.id_comp,
    Category.comp_id, Category.comp_id, Category.id_comp]

/-- The universal derived lift of a transformation from an exact functor. -/
def canonicalModelAugmentation
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (E F : B ⥤ C) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [F.Additive] {P : CochainComplex B ℤ → Prop}
    (D : DerivedReductionModelData F P) (τ : E ⟶ F) :
    E.mapDerivedCategory ⟶ D.reduction :=
  letI := D.isLeftDerived
  D.reduction.leftDerivedLift D.counit (HomotopyCategory.quasiIso B (.up ℤ))
    E.mapDerivedCategory (E.mapDerivedCategoryFactorsh.hom ≫
      Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (.up ℤ)) DerivedCategory.Qh)

set_option backward.isDefEq.respectTransparency false in
private theorem modelAugmentation_existsUnique
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (E F : B ⥤ C) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [F.Additive] {P : CochainComplex B ℤ → Prop}
    (D : DerivedReductionModelData F P) (τ : E ⟶ F)
    (hrep : ∀ K : DerivedCategory B,
      ∃ (R : CochainComplex B ℤ), P R ∧ Nonempty (DerivedCategory.Q.obj R ≅ K)) :
    ∃! η : E.mapDerivedCategory ⟶ D.reduction,
      ∀ (R : CochainComplex B ℤ), P R →
        η.app (DerivedCategory.Q.obj R) ≫ D.complexCounit R =
          E.mapDerivedCategoryFactors.hom.app R ≫
            DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app R) := by
  let W := HomotopyCategory.quasiIso B (.up ℤ)
  let : D.reduction.IsLeftDerivedFunctor D.counit W := D.isLeftDerived
  let α : DerivedCategory.Qh ⋙ E.mapDerivedCategory ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    E.mapDerivedCategoryFactorsh.hom ≫
      Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (.up ℤ)) DerivedCategory.Qh
  let η := D.reduction.leftDerivedLift D.counit W E.mapDerivedCategory α
  have hη (R : CochainComplex B ℤ) :
      η.app (DerivedCategory.Q.obj R) ≫ D.complexCounit R =
        E.mapDerivedCategoryFactors.hom.app R ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app R) := by
    exact lift_complex_fac E F D.reduction D.counit τ η
      (fun K ↦ D.reduction.leftDerived_fac_app D.counit W E.mapDerivedCategory α K) R
  refine ⟨η, fun R _ ↦ hη R, ?_⟩
  intro η' hη'
  apply NatTrans.ext
  funext K
  obtain ⟨R, hR, ⟨e⟩⟩ := hrep K
  have : IsIso (D.complexCounit R) := D.complexCounit_isIso R hR
  have heq : η'.app (DerivedCategory.Q.obj R) = η.app (DerivedCategory.Q.obj R) := by
    apply (cancel_mono (D.complexCounit R)).mp
    exact (hη' R hR).trans (hη R).symm
  apply (cancel_epi (E.mapDerivedCategory.map e.hom)).mp
  erw [η'.naturality, η.naturality, heq]

set_option backward.isDefEq.respectTransparency false in
/-- The derived quotient augmentation is uniquely fixed by the ordinary quotient unit. -/
theorem augmentation_existsUnique (T : Scheme.{t}) :
    ∃! η : diagonal (A := A) T ⟶ reduction d T,
      ∀ P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
          (R := exchangeConstantRing T A) P →
        η.app (DerivedCategory.Q.obj P) ≫ reductionComplexCounit d T P =
          (Functor.const ℕᵒᵖ).mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex (ordinaryAugmentation d T) (.up ℤ)).app P) := by
  let E : reductionModules T (exchangeConstantRing T A) ⥤
      exchangeTowers T (exchangeConstantRing T A) := Functor.const ℕᵒᵖ
  have hrep (K : D (A := A) T) :
      ∃ P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := exchangeConstantRing T A) P ∧
          Nonempty (DerivedCategory.Q.obj P ≅ K) := by
    let G := DerivedCategory.Q.objPreimage K
    obtain ⟨P, p, hP, _, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients G
    let : QuasiIso p := hp
    exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map p) ≪≫
      DerivedCategory.Q.objObjPreimageIso K⟩⟩
  exact modelAugmentation_existsUnique E (reductionModule d T) (reductionData d T)
    (ordinaryAugmentation d T) hrep

/-- The specified derived quotient augmentation. -/
def augmentation (T : Scheme.{t}) : diagonal (A := A) T ⟶ reduction d T :=
  canonicalModelAugmentation (Functor.const ℕᵒᵖ) (reductionModule d T)
    (reductionData d T) (ordinaryAugmentation d T)

/-- The canonical quotient completion unit, from the diagonal/limit adjunction. -/
def unit (T : Scheme.{t}) : 𝟭 (D (A := A) T) ⟶ completion d T :=
  (diagonalAdjunction (A := A) T).unit ≫
    Functor.whiskerRight (augmentation d T) (rlim (A := A) T)

/-- Completeness means invertibility of this specific quotient completion unit. -/
def IsComplete (T : Scheme.{t}) (K : D (A := A) T) : Prop := IsIso ((unit d T).app K)

/-- The full derived-complete category, with all ambient morphisms. -/
abbrev Complete (T : Scheme.{t}) := ObjectProperty.FullSubcategory (IsComplete d T)

/-- Ordinary constant-coefficient derived pullback, in the recorded ringed presentation. -/
abbrev pull {U V : Scheme.{t}} (f : U ⟶ V) :=
  proEtaleRingDerivedPullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
    (exchangeConstantIso f A)

/-- Ordinary constant-coefficient derived direct image, with its canonical derived unit. -/
abbrev push {U V : Scheme.{t}} (f : U ⟶ V) :=
  proEtaleRingDerivedDirectImage f (exchangeConstantRing V A) (exchangeConstantRing U A)
    (exchangeConstantIso f A)

/-- Completed pullback on ambient objects is ordinary pullback followed by completion. -/
def completePull {U V : Scheme.{t}} (f : U ⟶ V) := pull (A := A) f ⋙ completion d U

end CompactQuotient

variable {U V : Scheme.{t}} (f : U ⟶ V)

/-- The ordinary scalar/pullback mate, in the inverse direction of chi. -/
def ordinaryReductionPullInv (n : ℕ) :
    proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A) ⋙ proEtaleRingExtension (quotient d U n) ⟶
      proEtaleRingExtension (quotient d V n) ⋙
        proEtaleRingModulePullback f (d.finiteRing V n) (d.finiteRing U n)
          (d.finiteRingIso f n) :=
  (mateEquiv (proEtaleRingExtensionAdjunction (quotient d V n))
    (proEtaleRingExtensionAdjunction (quotient d U n))).symm
      (proEtaleRingRestrictionPullbackInv f (exchangeConstantRing V A) (d.finiteRing V n)
        (exchangeConstantRing U A) (d.finiteRing U n) (quotient d V n) (quotient d U n)
          (exchangeConstantIso f A) (d.finiteRingIso f n) (quotient_comm d f n))

section ScalarPullComparison
attribute [local irreducible] pbcScalarAdjunction proEtaleRingModuleAdjunction
attribute [local irreducible] completedAdicChange

set_option backward.isDefEq.respectTransparency false in
private theorem scalarPull_isIso {X Y : Scheme.{t}} (f : X ⟶ Y)
    (RV SV : Sheaf (ProEt.topology Y) CommRingCat.{t + 1})
    (RU SU : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj SV ≅ SU)
    (comm : cR.hom ≫ aU =
      (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map aV ≫ cS.hom) :
    IsIso ((mateEquiv (proEtaleRingExtensionAdjunction aV)
      (proEtaleRingExtensionAdjunction aU)).symm
        (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm)) := by
  let δ := proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm
  have hm : (mateEquiv (proEtaleRingModuleAdjunction f SV SU cS)
      (proEtaleRingModuleAdjunction f RV RU cR)
      (TwoSquare.mk _ _ _ _
        (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm))) =
      δ.hom := by
    exact restrictionPullback_mate f RV SV RU SU aV aU cR cS comm
  have hi : TwoSquare.mk _ _ _ _
      (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm) =
      (mateEquiv (proEtaleRingModuleAdjunction f SV SU cS)
        (proEtaleRingModuleAdjunction f RV RU cR)).symm
          (TwoSquare.mk _ _ _ _ δ.hom) := by
    apply (mateEquiv (proEtaleRingModuleAdjunction f SV SU cS)
      (proEtaleRingModuleAdjunction f RV RU cR)).injective
    rw [Equiv.apply_symm_apply]
    refine NatTrans.ext (funext fun M ↦ ?_)
    exact congr_app hm M
  change IsIso ((mateEquiv (proEtaleRingExtensionAdjunction aV)
    (proEtaleRingExtensionAdjunction aU)).symm
      (TwoSquare.mk _ _ _ _
        (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm)))
  rw [hi, iterated_mateEquiv_conjugateEquiv_symm]
  exact conjugateEquiv_symm_iso
    ((proEtaleRingExtensionAdjunction aV).comp
      (proEtaleRingModuleAdjunction f SV SU cS))
    ((proEtaleRingModuleAdjunction f RV RU cR).comp
      (proEtaleRingExtensionAdjunction aU)) δ.hom

set_option backward.isDefEq.respectTransparency false in
/-- The normalized ordinary mate is the invertible tensor balancing map. -/
theorem ordinaryReductionPullInv_isIso (n : ℕ) :
    IsIso (ordinaryReductionPullInv d f n) := by
  exact scalarPull_isIso f _ _ _ _ (quotient d V n) (quotient d U n)
    (exchangeConstantIso f A) (d.finiteRingIso f n) (quotient_comm d f n)

end ScalarPullComparison

attribute [instance] ordinaryReductionPullInv_isIso

/-- The ordinary reduction-level comparison after restriction to completed coefficients. -/
def levelPullIso (n : ℕ) :
    level d V n ⋙
        proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
          (exchangeConstantIso f A) ≅
      proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A) ⋙ level d U n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (proEtaleRingExtension (quotient d V n))
      (@asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv f
        (exchangeConstantRing V A) (d.finiteRing V n) (exchangeConstantRing U A) (d.finiteRing U n)
        (quotient d V n) (quotient d U n) (exchangeConstantIso f A)
        (d.finiteRingIso f n) (quotient_comm d f n))
        (proEtaleRingRestrictionPullbackInv_isIso f
          (exchangeConstantRing V A) (d.finiteRing V n)
          (exchangeConstantRing U A) (d.finiteRing U n)
          (quotient d V n) (quotient d U n) (exchangeConstantIso f A)
          (d.finiteRingIso f n) (quotient_comm d f n))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (ordinaryReductionPullInv d f n)).symm
      (proEtaleRingRestrictScalars (quotient d U n)) ≪≫
    Functor.associator _ _ _

section TowerPullTransition
set_option backward.isDefEq.respectTransparency false

private theorem mate_units
    {A B C E : Type*} [Category A] [Category B] [Category C] [Category E]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ E} {R₂ : E ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (P : A ⥤ C) (Q : B ⥤ E) (β : R₁ ⋙ P ⟶ Q ⋙ R₂)
    (X : A)
    [IsIso (((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ β)).app X)] :
    P.map (adj₁.unit.app X) ≫ β.app (L₁.obj X) ≫
      R₂.map (inv (((mateEquiv adj₁ adj₂).symm
        (TwoSquare.mk _ _ _ _ β)).app X)) = adj₂.unit.app (P.obj X) := by
  have h := unit_mateEquiv_symm adj₁ adj₂ (TwoSquare.mk _ _ _ _ β) X
  dsimp only [Functor.id_obj] at h
  rw [← Category.assoc, h, Category.assoc, ← R₂.map_comp,
    IsIso.hom_inv_id, R₂.map_id]
  erw [Category.comp_id]

private theorem levelPullIso_unit (n : ℕ)
    (M : reductionModules V (exchangeConstantRing V A)) :
    (proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A)).map
        ((proEtaleRingExtensionAdjunction (quotient d V n)).unit.app M) ≫
      (levelPullIso d f n).hom.app M =
        (proEtaleRingExtensionAdjunction (quotient d U n)).unit.app
          ((proEtaleRingModulePullback f (exchangeConstantRing V A)
            (exchangeConstantRing U A) (exchangeConstantIso f A)).obj M) := by
  have : IsIso (((mateEquiv
      (proEtaleRingExtensionAdjunction (quotient d V n))
      (proEtaleRingExtensionAdjunction (quotient d U n))).symm
        (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionPullbackInv f
          (exchangeConstantRing V A) (d.finiteRing V n) (exchangeConstantRing U A)
          (d.finiteRing U n) (quotient d V n) (quotient d U n)
          (exchangeConstantIso f A) (d.finiteRingIso f n) (quotient_comm d f n)))).app M) := by
    change IsIso ((ordinaryReductionPullInv d f n).app M)
    infer_instance
  simp only [levelPullIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, asIso_hom, asIso_inv, Iso.symm_hom,
    Category.id_comp, Category.comp_id, NatIso.isIso_inv_app, ordinaryReductionPullInv]
  erw [Category.id_comp]
  exact mate_units (proEtaleRingExtensionAdjunction (quotient d V n))
      (proEtaleRingExtensionAdjunction (quotient d U n)) _ _
      (proEtaleRingRestrictionPullbackInv f (exchangeConstantRing V A) (d.finiteRing V n)
        (exchangeConstantRing U A) (d.finiteRing U n) (quotient d V n) (quotient d U n)
        (exchangeConstantIso f A) (d.finiteRingIso f n) (quotient_comm d f n)) M

private theorem restrictionPullback_unit
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (RU SU : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj SV ≅ SU)
    (comm : cR.hom ≫ aU =
      (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map aV ≫ cS.hom)
    (N : proEtaleRingModules V SV) (W : V.ProEtᵒᵖ) (z : N.val.obj W) :
    ((proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm).app N).val.app
        ((proEtaleBaseChange f).op.obj W)
        (((proEtaleRingModuleAdjunction f RV RU cR).unit.app
          ((proEtaleRingRestrictScalars aV).obj N)).val.app W z) =
      ((proEtaleRingModuleAdjunction f SV SU cS).unit.app N).val.app W z := by
  let δ := proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm
  let σ := proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm
  have h := unit_mateEquiv (proEtaleRingModuleAdjunction f SV SU cS)
    (proEtaleRingModuleAdjunction f RV RU cR) (TwoSquare.mk _ _ _ _ σ) N
  have hm := restrictionPullback_mate f RV SV RU SU aV aU cR cS comm
  change (proEtaleRingRestrictScalars aV).map
      ((proEtaleRingModuleAdjunction f SV SU cS).unit.app N) ≫
        (mateEquiv (proEtaleRingModuleAdjunction f SV SU cS)
          (proEtaleRingModuleAdjunction f RV RU cR)
          (TwoSquare.mk _ _ _ _ σ)).app _ = _ at h
  rw [hm] at h
  have hz := congrArg (fun k ↦ k.val.app W z) h
  change (δ.hom.app ((proEtaleRingModulePullback f SV SU cS).obj N)).val.app W
      (((proEtaleRingModuleAdjunction f SV SU cS).unit.app N).val.app W z) = _ at hz
  have he := (Classical.choose_spec
    (proEtaleRingRestrictionDirectImage_existsUnique f RV SV RU SU aV aU cR cS comm)).1
      ((proEtaleRingModulePullback f SV SU cS).obj N) W
      (((proEtaleRingModuleAdjunction f SV SU cS).unit.app N).val.app W z)
  exact (he.symm.trans hz).symm

private theorem levelPullIso_one (n : ℕ)
    (M : reductionModules V (exchangeConstantRing V A))
    (W : V.ProEtᵒᵖ) (x : M.val.obj W) :
    ((levelPullIso d f n).hom.app M).val.app ((proEtaleBaseChange f).op.obj W)
        (((proEtaleRingModuleAdjunction f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).unit.app
            ((level d V n).obj M)).val.app W
              (reductionTensorSection V (quotient d V n) M W 1 x)) =
      reductionTensorSection U (quotient d U n)
        ((proEtaleRingModulePullback f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).obj M)
        ((proEtaleBaseChange f).op.obj W) 1
        (((proEtaleRingModuleAdjunction f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).unit.app M).val.app W x) := by
  let P := proEtaleRingModulePullback f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A)
  let Q := proEtaleRingModuleDirectImage f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A)
  let adj := proEtaleRingModuleAdjunction f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A)
  let uV := (proEtaleRingExtensionAdjunction (quotient d V n)).unit.app M
  let uU := (proEtaleRingExtensionAdjunction (quotient d U n)).unit.app (P.obj M)
  have h : uV ≫ adj.unit.app ((level d V n).obj M) ≫
      Q.map ((levelPullIso d f n).hom.app M) = adj.unit.app M ≫ Q.map uU := by
    erw [← adj.unit_naturality_assoc]
    rw [← Q.map_comp]
    exact congrArg (adj.unit.app M ≫ ·) (congrArg Q.map (levelPullIso_unit d f n M))
  have hv : uV.val.app W x = reductionTensorSection V (quotient d V n) M W 1 x := by
    exact (pbcScalarAdjunction_exists (quotient d V n)).exists.choose_spec M W x
  have hu : uU.val.app ((proEtaleBaseChange f).op.obj W)
        ((adj.unit.app M).val.app W x) =
      reductionTensorSection U (quotient d U n) (P.obj M)
        ((proEtaleBaseChange f).op.obj W) 1 ((adj.unit.app M).val.app W x) := by
    exact (pbcScalarAdjunction_exists (quotient d U n)).exists.choose_spec
      (P.obj M) ((proEtaleBaseChange f).op.obj W) ((adj.unit.app M).val.app W x)
  have hx := congrArg (fun k ↦ k.val.app W x) h
  change ((levelPullIso d f n).hom.app M).val.app ((proEtaleBaseChange f).op.obj W)
      ((adj.unit.app ((level d V n).obj M)).val.app W (uV.val.app W x)) =
    uU.val.app ((proEtaleBaseChange f).op.obj W) ((adj.unit.app M).val.app W x) at hx
  rw [hv, hu] at hx
  exact hx

open AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization in
private theorem levelPullIso_tensor (n : ℕ)
    (M : reductionModules V (exchangeConstantRing V A))
    (W : V.ProEtᵒᵖ) (s : (d.finiteRing V n).obj.obj W) (x : M.val.obj W) :
    ((levelPullIso d f n).hom.app M).val.app ((proEtaleBaseChange f).op.obj W)
        (((proEtaleRingModuleAdjunction f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).unit.app
            ((level d V n).obj M)).val.app W
              (reductionTensorSection V (quotient d V n) M W s x)) =
      reductionTensorSection U (quotient d U n)
        ((proEtaleRingModulePullback f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).obj M)
        ((proEtaleBaseChange f).op.obj W)
        ((proEtaleRingDirectImageMap f (d.finiteRing V n) (d.finiteRing U n)
          (d.finiteRingIso f n)).hom.app W s)
        (((proEtaleRingModuleAdjunction f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).unit.app M).val.app W x) := by
  let σ := proEtaleRingRestrictionPullbackInv f (exchangeConstantRing V A) (d.finiteRing V n)
    (exchangeConstantRing U A) (d.finiteRing U n) (quotient d V n) (quotient d U n)
    (exchangeConstantIso f A) (d.finiteRingIso f n) (quotient_comm d f n)
  let N := (proEtaleRingExtension (quotient d V n)).obj M
  let g := (inv (ordinaryReductionPullInv d f n)).app M
  let adjR := proEtaleRingModuleAdjunction f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A)
  let adjS := proEtaleRingModuleAdjunction f (d.finiteRing V n)
    (d.finiteRing U n) (d.finiteRingIso f n)
  let B := (proEtaleBaseChange f).op.obj W
  have hσ (z : N.val.obj W) :
      (σ.app N).val.app B ((adjR.unit.app ((level d V n).obj M)).val.app W z) =
        ((adjS.unit.app N).val.app W z) :=
    restrictionPullback_unit f _ _ _ _ _ _ _ _ _ N W z
  have h1 := levelPullIso_one d f n M W x
  change (g.val.app B) ((σ.app N).val.app B
    ((adjR.unit.app ((level d V n).obj M)).val.app W
      (reductionTensorSection V (quotient d V n) M W 1 x))) = _ at h1
  rw [hσ] at h1
  change (g.val.app B) ((σ.app N).val.app B
    ((adjR.unit.app ((level d V n).obj M)).val.app W
      (reductionTensorSection V (quotient d V n) M W s x))) = _
  rw [hσ]
  have hs := tensorSection_smul V (quotient d V n) M W s 1 x
  rw [mul_one] at hs
  rw [← hs]
  have hsm := ((adjS.unit.app N).val.app W).hom.map_smul s
    (reductionTensorSection V (quotient d V n) M W 1 x)
  change (adjS.unit.app N).val.app W
      (s • reductionTensorSection V (quotient d V n) M W 1 x) =
    @SMul.smul ((d.finiteRing U n).obj.obj B)
      (((proEtaleRingModulePullback f (d.finiteRing V n) (d.finiteRing U n)
        (d.finiteRingIso f n)).obj N).val.obj B) inferInstance
      ((proEtaleRingDirectImageMap f (d.finiteRing V n) (d.finiteRing U n)
        (d.finiteRingIso f n)).hom.app W s)
      ((adjS.unit.app N).val.app W
        (reductionTensorSection V (quotient d V n) M W 1 x)) at hsm
  rw [hsm]
  erw [(g.val.app B).hom.map_smul]
  rw [h1]
  simpa only [mul_one] using tensorSection_smul U (quotient d U n)
    ((proEtaleRingModulePullback f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A)).obj M) B
    ((proEtaleRingDirectImageMap f (d.finiteRing V n) (d.finiteRing U n)
      (d.finiteRingIso f n)).hom.app W s) 1
    ((adjR.unit.app M).val.app W x)

private theorem finiteRingIso_transition (n : ℕ) :
    (d.finiteRingIso f (n + 1)).hom ≫
      reductionCoefficientMap U d (n + 1) n (Nat.le_succ n) =
    (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
      (reductionCoefficientMap V d (n + 1) n (Nat.le_succ n)) ≫
        (d.finiteRingIso f n).hom := by
  let a : op (n + 1) ⟶ op n := (homOfLE (Nat.le_succ n)).op
  change (d.finiteRingIso f (n + 1)).hom ≫ (reductionCoefficientSystem U d).map a =
    (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
      ((reductionCoefficientSystem V d).map a) ≫ (d.finiteRingIso f n).hom
  let eU := pbcConstantSystemComparison U d
  let eV := pbcConstantSystemComparison V d
  let b : adicLisseRingSystem V d.ideal ⋙
      proEtaleSheafInverseImage f CommRingCat.{t + 1} ⟶
      adicLisseRingSystem U d.ideal :=
    NatTrans.ofOpSequence (fun k ↦ (proEtaleConstantComparison f).app
      (CommRingCat.of (A ⧸ d.ideal ^ (k + 1)))) (by
        intro k
        simpa only [Functor.comp_map, adicLisseRingSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          (proEtaleConstantComparison f).naturality
            (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (k + 1))))
  have hn := congrArg (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
    (eV.inv.naturality a)
  have hb := b.naturality a
  have hu := eU.hom.naturality a
  simp only [Functor.map_comp] at hn
  change (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
      ((reductionCoefficientSystem V d).map a) ≫
        (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
          (pbcLevelConstantComparison V d n).inv =
    (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
      (pbcLevelConstantComparison V d (n + 1)).inv ≫
        (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
          ((adicLisseRingSystem V d.ideal).map a) at hn
  change (adicLisseRingSystem V d.ideal ⋙
    proEtaleSheafInverseImage f CommRingCat.{t + 1}).map a ≫
      (proEtaleConstantComparison f).app (d.ringTower.obj (op n)) =
    (proEtaleConstantComparison f).app (d.ringTower.obj (op (n + 1))) ≫
      (adicLisseRingSystem U d.ideal).map a at hb
  change (adicLisseRingSystem U d.ideal).map a ≫
      (pbcLevelConstantComparison U d n).hom =
    (pbcLevelConstantComparison U d (n + 1)).hom ≫
      (reductionCoefficientSystem U d).map a at hu
  dsimp only [AdicCoefficientDatum.finiteRingIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom]
  simp only [Category.assoc]
  erw [← hu]
  rw [← Category.assoc _ _ ((pbcLevelConstantComparison U d n).hom)]
  rw [← hb]
  simp only [Functor.comp_map, Category.assoc]
  rw [← reassoc_of% hn]

open AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization in
private theorem levelPullIso_step (n : ℕ)
    (M : reductionModules V (exchangeConstantRing V A)) :
    (proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A)).map ((step d V n).app M) ≫
        (levelPullIso d f n).hom.app M =
      (levelPullIso d f (n + 1)).hom.app M ≫
        (step d U n).app ((proEtaleRingModulePullback f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).obj M) := by
  let adj := proEtaleRingModuleAdjunction f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A)
  apply (adj.homEquiv _ _).injective
  apply level_hom_ext V (quotient d V (n + 1)) M
  intro W s x
  let B := (proEtaleBaseChange f).op.obj W
  let P := proEtaleRingModulePullback f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A)
  have hn := congrArg (fun k ↦ k.val.app W
      (reductionTensorSection V (quotient d V (n + 1)) M W s x))
    (adj.unit.naturality ((step d V n).app M))
  change (adj.unit.app ((level d V n).obj M)).val.app W
      (((step d V n).app M).val.app W
        (reductionTensorSection V (quotient d V (n + 1)) M W s x)) =
    ((P.map ((step d V n).app M)).val.app B)
      ((adj.unit.app ((level d V (n + 1)).obj M)).val.app W
        (reductionTensorSection V (quotient d V (n + 1)) M W s x)) at hn
  change ((levelPullIso d f n).hom.app M).val.app B
      (((P.map ((step d V n).app M)).val.app B)
        ((adj.unit.app ((level d V (n + 1)).obj M)).val.app W
          (reductionTensorSection V (quotient d V (n + 1)) M W s x))) =
    ((step d U n).app (P.obj M)).val.app B
      (((levelPullIso d f (n + 1)).hom.app M).val.app B
        ((adj.unit.app ((level d V (n + 1)).obj M)).val.app W
          (reductionTensorSection V (quotient d V (n + 1)) M W s x)))
  rw [← hn]
  erw [(step_existsUnique d V n).exists.choose_spec]
  rw [levelPullIso_tensor, levelPullIso_tensor]
  erw [(step_existsUnique d U n).exists.choose_spec]
  have hq := congrArg (fun z ↦ z.hom.app W s)
    (restrictionDirectImageMap_square f (d.finiteRing V (n + 1)) (d.finiteRing V n)
      (d.finiteRing U (n + 1)) (d.finiteRing U n)
      (reductionCoefficientMap V d (n + 1) n (Nat.le_succ n))
      (reductionCoefficientMap U d (n + 1) n (Nat.le_succ n))
      (d.finiteRingIso f (n + 1)) (d.finiteRingIso f n) (finiteRingIso_transition d f n))
  exact congrArg (fun z ↦ reductionTensorSection U (quotient d U n) (P.obj M) B z
    ((adj.unit.app M).val.app W x)) hq

/-- The level tensor comparisons commute with every quotient transition, including identities. -/
theorem levelPullIso_transition
    (M : reductionModules V (exchangeConstantRing V A)) {n m : ℕᵒᵖ} (a : n ⟶ m) :
    ((reductionModule d V ⋙ exchangeTowerModulePull f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).obj M).map a ≫
        (levelPullIso d f m.unop).hom.app M =
      (levelPullIso d f n.unop).hom.app M ≫
        ((proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
          (exchangeConstantIso f A) ⋙ reductionModule d U).obj M).map a := by
  let η : (reductionModule d V ⋙ exchangeTowerModulePull f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).obj M ⟶
      (proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
          (exchangeConstantIso f A) ⋙ reductionModule d U).obj M :=
    NatTrans.ofOpSequence (fun n ↦ (levelPullIso d f n).hom.app M) (by
      intro n
      change (proEtaleRingModulePullback f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).map
            (((Functor.ofOpSequence (step d V)).map
              (homOfLE (n.le_add_right 1)).op).app M) ≫ _ =
        _ ≫ ((Functor.ofOpSequence (step d U)).map
          (homOfLE (n.le_add_right 1)).op).app _
      rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
      exact levelPullIso_step d f n M)
  exact η.naturality a

end TowerPullTransition

/-- The actual strict tower isomorphism of ordinary tensor/pullback computations. -/
def ordinaryReductionPullIso :
    reductionModule d V ⋙ exchangeTowerModulePull f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A) ≅
      proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A) ⋙ reductionModule d U :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents
      (fun n ↦ (levelPullIso d f n.unop).app M)
      (fun a ↦ levelPullIso_transition d f M a))
    (fun a ↦ by
      apply NatTrans.ext
      funext n
      exact (levelPullIso d f n.unop).hom.naturality a)

section ModelPullNormalization

variable {B C T U : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
  [Category T] [Abelian T] [Category U] [Abelian U]
  [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory T] [HasDerivedCategory U]
  (F : B ⥤ T) [F.Additive] (G : C ⥤ U) [G.Additive]
  (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (H : T ⥤ U) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  {M : CochainComplex B ℤ → Prop} {N : CochainComplex C ℤ → Prop}
  (DF : DerivedReductionModelData F M) (DG : DerivedReductionModelData G N)
  (e : F ⋙ H ≅ P ⋙ G)

set_option linter.defProp false in
/-- Counit normalization for an exact square of derived models. -/
def ModelPullNormalized
    (η : DF.reduction ⋙ H.mapDerivedCategory ≅ P.mapDerivedCategory ⋙ DG.reduction) : Prop :=
      ∀ K : CochainComplex B ℤ, M K →
        η.hom.app (DerivedCategory.Q.obj K) ≫
          DG.reduction.map (P.mapDerivedCategoryFactors.hom.app K) ≫
            DG.complexCounit ((P.mapHomologicalComplex (.up ℤ)).obj K) =
        H.mapDerivedCategory.map (DF.complexCounit K) ≫
          H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K)

end ModelPullNormalization

set_option linter.defProp false in
/-- The strict ordinary comparison and universal counits fix the derived comparison. -/
def ReductionPullNormalized
    (τ : reduction d V ⋙ exchangeConstantPull (A := A) f ≅
        pull (A := A) f ⋙ reduction d U) : Prop :=
  ModelPullNormalized (reductionModule d V) (reductionModule d U)
    (proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))
    (exchangeTowerModulePull f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))
    (reductionData d V) (reductionData d U) (ordinaryReductionPullIso d f) τ

section DerivedPullComparison
set_option backward.isDefEq.respectTransparency false

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem restrictionLocalization
    {A : Type*} [Category A] {D : Type*} [Category D]
    (W : MorphismProperty A) [W.HasRightCalculusOfFractions]
    (L : A ⥤ D) [L.IsLocalization W] (P : ObjectProperty A)
    (res : ∀ X : A, ∃ (Y : P.FullSubcategory) (s : Y.obj ⟶ X), W s) :
    (P.ι ⋙ L).IsLocalization (W.inverseImage P.ι) := by
  let V := W.inverseImage P.ι
  obtain ⟨_, F, hF, ⟨e⟩⟩ :=
    rightFractionDenseSubcategory W inferInstance P res L V.Q
  have : F.IsEquivalence := hF
  have : (V.Q ⋙ F).IsLocalization V := inferInstance
  exact Functor.IsLocalization.of_iso V e

private theorem descendUnit
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : ObjectProperty C) (L : C ⥤ D) (W : MorphismProperty C)
    [(P.ι ⋙ L).IsLocalization (W.inverseImage P.ι)]
    (F G : D ⥤ E) (R : C ⥤ E) (α : L ⋙ F ⟶ R) (γ : L ⋙ G ⟶ R)
    (hγ : ∀ X : P.FullSubcategory, IsIso (γ.app X.obj)) :
    ∃! η : F ⟶ G, ∀ X : P.FullSubcategory,
      η.app (L.obj X.obj) = α.app X.obj ≫ inv (γ.app X.obj) := by
  let S := P.ι ⋙ L
  let V := W.inverseImage P.ι
  let τ : S ⋙ F ⟶ S ⋙ G :=
    { app := fun X ↦ α.app X.obj ≫ inv (γ.app X.obj)
      naturality := by
        intro X Y f
        change (L ⋙ F).map f.hom ≫ α.app Y.obj ≫ inv (γ.app Y.obj) =
          (α.app X.obj ≫ inv (γ.app X.obj)) ≫ (L ⋙ G).map f.hom
        rw [← Category.assoc, α.naturality, Category.assoc, Category.assoc]
        apply congrArg (α.app X.obj ≫ ·)
        apply (cancel_mono (γ.app Y.obj)).1
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        rw [γ.naturality f.hom]
        simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] }
  let E' := (Functor.whiskeringLeft P.FullSubcategory D E).obj S
  have : E'.Full := Localization.full_whiskeringLeft S V E
  refine ⟨E'.preimage τ, ?_, ?_⟩
  · intro X
    exact congrArg (fun k ↦ k.app X) (E'.map_preimage τ)
  · intro θ hθ
    apply Localization.natTrans_ext S V
    intro X
    exact (hθ X).trans (congrArg (fun k ↦ k.app X) (E'.map_preimage τ)).symm

private theorem descendIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : ObjectProperty C) (L : C ⥤ D) (W : MorphismProperty C)
    [(P.ι ⋙ L).IsLocalization (W.inverseImage P.ι)]
    (F G : D ⥤ E) (R : C ⥤ E) (α : L ⋙ F ⟶ R) (γ : L ⋙ G ⟶ R)
    (hα : ∀ X : P.FullSubcategory, IsIso (α.app X.obj))
    (hγ : ∀ X : P.FullSubcategory, IsIso (γ.app X.obj)) :
    ∃! η : F ≅ G, ∀ X : P.FullSubcategory,
      η.hom.app (L.obj X.obj) ≫ γ.app X.obj = α.app X.obj := by
  let S := P.ι ⋙ L
  let V := W.inverseImage P.ι
  obtain ⟨η, hη, hu⟩ := descendUnit P L W F G R α γ hγ
  let T := (Functor.whiskeringLeft P.FullSubcategory D E).obj S
  let : T.Full := Localization.full_whiskeringLeft S V E
  let : T.Faithful := Localization.faithful_whiskeringLeft S V E
  have happ (X : P.FullSubcategory) : IsIso ((T.map η).app X) := by
    change IsIso (η.app (L.obj X.obj))
    rw [hη X]
    let := hα X
    let := hγ X
    infer_instance
  have hT : IsIso (T.map η) := NatIso.isIso_of_isIso_app _
  let : IsIso η := isIso_of_reflects_iso η T
  refine ⟨asIso η, ?_, ?_⟩
  · intro X
    change η.app (L.obj X.obj) ≫ γ.app X.obj = _
    rw [hη X]
    let := hγ X
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  · intro η' hη'
    apply Iso.ext
    apply hu η'.hom
    intro X
    let := hγ X
    apply (cancel_mono (γ.app X.obj)).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact hη' X

private theorem descendIso_from_resolving
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P P₀ : ObjectProperty C) (L : C ⥤ D) (W : MorphismProperty C)
    [W.HasRightCalculusOfFractions] [L.IsLocalization W]
    (res : ∀ X : C, ∃ (Y : P₀.FullSubcategory) (s : Y.obj ⟶ X), W s)
    (hP : ∀ X, P₀ X → P X)
    (F G : D ⥤ E) (R : C ⥤ E) (α : L ⋙ F ⟶ R) (γ : L ⋙ G ⟶ R)
    (hα : ∀ X : P.FullSubcategory, IsIso (α.app X.obj))
    (hγ : ∀ X : P₀.FullSubcategory, IsIso (γ.app X.obj)) :
    ∃! η : F ≅ G, ∀ X : P.FullSubcategory,
      η.hom.app (L.obj X.obj) ≫ γ.app X.obj = α.app X.obj := by
  have hres (X : C) : ∃ (Y : P.FullSubcategory) (s : Y.obj ⟶ X), W s := by
    obtain ⟨Y, s, hs⟩ := res X
    exact ⟨⟨Y.obj, hP Y.obj Y.property⟩, s, hs⟩
  let : (P.ι ⋙ L).IsLocalization (W.inverseImage P.ι) :=
    restrictionLocalization W L P hres
  have hγ' (X : P.FullSubcategory) : IsIso (γ.app X.obj) := by
    obtain ⟨Y, s, hs⟩ := res X.obj
    let : IsIso (L.map s) := Localization.inverts L W s hs
    let : IsIso (α.app X.obj) := hα X
    let : IsIso (α.app Y.obj) := hα ⟨Y.obj, hP Y.obj Y.property⟩
    have hi : IsIso (α.app Y.obj ≫ R.map s) := by
      rw [← α.naturality s]
      change IsIso (F.map (L.map s) ≫ α.app X.obj)
      infer_instance
    let : IsIso (R.map s) := IsIso.of_isIso_comp_left (α.app Y.obj) (R.map s)
    let : IsIso (γ.app Y.obj) := hγ Y
    have hi' : IsIso ((L ⋙ G).map s ≫ γ.app X.obj) := by
      rw [γ.naturality s]
      infer_instance
    have : IsIso ((L ⋙ G).map s) := by
      change IsIso (G.map (L.map s))
      infer_instance
    exact IsIso.of_isIso_comp_left ((L ⋙ G).map s) (γ.app X.obj)
  exact descendIso P L W F G R α γ hα hγ'

section ModelPull
variable {B C T U : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
  [Category T] [Abelian T] [Category U] [Abelian U]
  [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory T] [HasDerivedCategory U]
  (F : B ⥤ T) [F.Additive] (G : C ⥤ U) [G.Additive]
  (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (H : T ⥤ U) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  {M : CochainComplex B ℤ → Prop} {N : CochainComplex C ℤ → Prop}
  (DF : DerivedReductionModelData F M) (DG : DerivedReductionModelData G N)
  (e : F ⋙ H ≅ P ⋙ G)

private abbrev modelPullCommon :=
  P.mapHomotopyCategory (.up ℤ) ⋙ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

private abbrev modelPullSourceCounit :
    DerivedCategory.Qh ⋙ (DF.reduction ⋙ H.mapDerivedCategory) ⟶
      modelPullCommon G P :=
  (Functor.associator _ _ _).inv ≫ Functor.whiskerRight DF.counit H.mapDerivedCategory ≫
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (F.mapHomotopyCategory (.up ℤ)) H.mapDerivedCategoryFactorsh.hom ≫
        (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight
            ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom ≫
              (Functor.mapHomotopyCategoryCompIso (Iso.refl (P ⋙ G)) (.up ℤ)).inv)
            DerivedCategory.Qh

private abbrev modelPullTargetCounit :
    DerivedCategory.Qh ⋙ (P.mapDerivedCategory ⋙ DG.reduction) ⟶
      modelPullCommon G P :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight P.mapDerivedCategoryFactorsh.hom DG.reduction ≫
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (P.mapHomotopyCategory (.up ℤ)) DG.counit ≫
          (Functor.associator _ _ _).inv

private theorem modelPullHomotopy_existsUnique
    (M₀ : CochainComplex B ℤ → Prop)
    (h₀ : ∀ K, M₀ K → M K)
    (res : ∀ K : CochainComplex B ℤ, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K),
      M₀ L ∧ QuasiIso s)
    (hmap : ∀ K, M₀ K → N ((P.mapHomologicalComplex (.up ℤ)).obj K)) :
    ∃! η : DF.reduction ⋙ H.mapDerivedCategory ≅ P.mapDerivedCategory ⋙ DG.reduction,
      ∀ K : CochainComplex B ℤ, M K →
        η.hom.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient B (.up ℤ)).obj K)) ≫
          (modelPullTargetCounit G P DG).app
            ((HomotopyCategory.quotient B (.up ℤ)).obj K) =
          (modelPullSourceCounit F G P H DF e).app
            ((HomotopyCategory.quotient B (.up ℤ)).obj K) := by
  let Q := HomotopyCategory.quotient B (.up ℤ)
  let S : ObjectProperty (HomotopyCategory B (.up ℤ)) :=
    fun K ↦ ∃ L : CochainComplex B ℤ, M L ∧ Q.obj L = K
  let S₀ : ObjectProperty (HomotopyCategory B (.up ℤ)) :=
    fun K ↦ ∃ L : CochainComplex B ℤ, M₀ L ∧ Q.obj L = K
  have hS (K) (hK : S₀ K) : S K := by
    obtain ⟨L, hL, rfl⟩ := hK
    exact ⟨L, h₀ L hL, rfl⟩
  have hr (K : HomotopyCategory B (.up ℤ)) :
      ∃ (L : S₀.FullSubcategory) (s : L.obj ⟶ K),
        HomotopyCategory.quasiIso B (.up ℤ) s := by
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    obtain ⟨L, s, hL, hs⟩ := res K
    exact ⟨⟨Q.obj L, L, hL, rfl⟩, Q.map s,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hα (K : S.FullSubcategory) :
      IsIso ((modelPullSourceCounit F G P H DF e).app K.obj) := by
    obtain ⟨L, hL, hLK⟩ := K.property
    let := DF.isIso_counit L hL
    rw [← hLK]
    simp only [modelPullSourceCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp]
    infer_instance
  have hγ (K : S₀.FullSubcategory) :
      IsIso ((modelPullTargetCounit G P DG).app K.obj) := by
    obtain ⟨L, hL, hLK⟩ := K.property
    rw [← hLK]
    have : IsIso (DG.counit.app ((P.mapHomotopyCategory (.up ℤ)).obj (Q.obj L))) := by
      change IsIso (DG.counit.app ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((P.mapHomologicalComplex (.up ℤ)).obj L)))
      exact DG.isIso_counit _ (hmap L hL)
    simp only [modelPullTargetCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    infer_instance
  obtain ⟨η, hη, hu⟩ := descendIso_from_resolving S S₀ DerivedCategory.Qh
    (HomotopyCategory.quasiIso B (.up ℤ)) hr hS
    (DF.reduction ⋙ H.mapDerivedCategory) (P.mapDerivedCategory ⋙ DG.reduction)
    (modelPullCommon G P) (modelPullSourceCounit F G P H DF e)
    (modelPullTargetCounit G P DG) hα hγ
  refine ⟨η, ?_, ?_⟩
  · intro K hK
    exact hη ⟨Q.obj K, K, hK, rfl⟩
  · intro η' hη'
    apply hu η'
    intro K
    obtain ⟨L, hL, hLK⟩ := K.property
    rw [← hLK]
    exact hη' L hL

private theorem modelPull_normalized_iff
    (η : DF.reduction ⋙ H.mapDerivedCategory ≅ P.mapDerivedCategory ⋙ DG.reduction)
    (K : CochainComplex B ℤ) :
    (η.hom.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient B (.up ℤ)).obj K)) ≫
        (modelPullTargetCounit G P DG).app
          ((HomotopyCategory.quotient B (.up ℤ)).obj K) =
      (modelPullSourceCounit F G P H DF e).app
        ((HomotopyCategory.quotient B (.up ℤ)).obj K)) ↔
    (η.hom.app (DerivedCategory.Q.obj K) ≫
        DG.reduction.map (P.mapDerivedCategoryFactors.hom.app K) ≫
          DG.complexCounit ((P.mapHomologicalComplex (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (DF.complexCounit K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K)) := by
  simp only [modelPullSourceCounit, modelPullTargetCounit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  rw [P.mapDerivedCategoryFactorsh_hom_app]
  erw [H.mapDerivedCategoryFactorsh_hom_app ((F.mapHomologicalComplex (.up ℤ)).obj K)]
  simp only [DerivedReductionModelData.complexCounit,
    AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.quotient_hom_id,
    AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.quotient_inv_id,
    AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.homotopyFactors_inv_id,
    Category.assoc]
  have hF : (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K =
      𝟙 ((HomotopyCategory.quotient T (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj K)) := rfl
  have hG : (G.mapHomotopyCategoryFactors (.up ℤ)).hom.app
      ((P.mapHomologicalComplex (.up ℤ)).obj K) =
      𝟙 ((HomotopyCategory.quotient U (.up ℤ)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj
          ((P.mapHomologicalComplex (.up ℤ)).obj K))) := rfl
  have he : DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app
          ((HomotopyCategory.quotient B (.up ℤ)).obj K) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (P ⋙ G)) (.up ℤ)).inv.app
          ((HomotopyCategory.quotient B (.up ℤ)).obj K)) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := by
    change DerivedCategory.Qh.map
      ((HomotopyCategory.quotient U (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app K) ≫
       (HomotopyCategory.quotient U (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ G)) (.up ℤ)).inv.app K)) = _
    rw [← Functor.map_comp]
    have hv : (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ G)) (.up ℤ)).inv.app K =
        𝟙 (((P ⋙ G).mapHomologicalComplex (.up ℤ)).obj K) := rfl
    rw [hv, Category.comp_id]
    rfl
  simp only [hF, hG, Functor.map_comp, Category.assoc, he]
  erw [P.mapDerivedCategory.map_id, (DerivedCategory.Qh (C := C)).map_id,
    DG.reduction.map_id, (DerivedCategory.Qh (C := U)).map_id,
    H.mapDerivedCategory.map_id, DF.reduction.map_id,
    (DerivedCategory.Qh (C := T)).map_id]
  erw [DG.reduction.map_id, H.mapDerivedCategory.map_id]
  repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
  erw [(DerivedCategory.Qh (C := U)).map_id, H.mapDerivedCategory.map_id]
  repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
  rfl

private theorem modelPull_existsUnique
    (M₀ : CochainComplex B ℤ → Prop)
    (h₀ : ∀ K, M₀ K → M K)
    (res : ∀ K : CochainComplex B ℤ, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K),
      M₀ L ∧ QuasiIso s)
    (hmap : ∀ K, M₀ K → N ((P.mapHomologicalComplex (.up ℤ)).obj K)) :
    ∃! η : DF.reduction ⋙ H.mapDerivedCategory ≅ P.mapDerivedCategory ⋙ DG.reduction,
      ModelPullNormalized F G P H DF DG e η := by
  obtain ⟨η, hη, hu⟩ := modelPullHomotopy_existsUnique F G P H DF DG e M₀ h₀ res hmap
  refine ⟨η, ?_, ?_⟩
  · intro K hK
    exact (modelPull_normalized_iff F G P H DF DG e η K).mp (hη K hK)
  · intro η' hη'
    apply hu η'
    intro K hK
    exact (modelPull_normalized_iff F G P H DF DG e η' K).mpr (hη' K hK)

end ModelPull

private theorem flatKFlatResolution (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (K : CochainComplex (proEtaleRingModules T R) ℤ) :
    ∃ (L : CochainComplex (proEtaleRingModules T R) ℤ) (s : L ⟶ K),
      (L.IsKFlatIndependentCoefficients ∧ ∀ n : ℤ,
        SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := R) (L.X n)) ∧
        QuasiIso s := by
  obtain ⟨L, s, hL, hflat, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  refine ⟨L, s, ⟨hL, ?_⟩, hs⟩
  intro n
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (L.X n)).symm (hflat n)

private theorem pullback_kFlat {U V : Scheme.{t}} (f : U ⟶ V)
    (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R ≅ S)
    (P : CochainComplex (proEtaleRingModules V R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ n : ℤ,
      SheafOfModules.IsFlatOnSite (J := ProEt.topology V) (R := R) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists f R
  have : PreservesFiniteLimits (proEtaleSheafInverseImage f (Type (t + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 V)).2.2.2.1
  let C := proEtaleRingModules V R
  let D := proEtaleRingModules U ((proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R)
  have hmap' (F : C ⥤ D) (h : I.modules = F) {N N' : C} (a : N ⟶ N') :
      SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} c.hom (F.obj N) (F.map a) =
        eqToHom (congrArg (fun G : C ⥤ D ↦
          SheafOfModules.changeOfRings.{t, t + 1, t + 1} c.hom (G.obj N)) h.symm) ≫
        SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} c.hom
          (I.modules.obj N) (I.modules.map a) ≫
        eqToHom (congrArg (fun G : C ⥤ D ↦
          SheafOfModules.changeOfRings.{t, t + 1, t + 1} c.hom (G.obj N')) h.symm).symm := by
    subst F
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (SheafOfModules.isKFlat_ringedToposPullback
    (proEtaleSheafInverseImage f (Type (t + 1)))
    (proEtaleSheafDirectImage f (Type (t + 1)))
    (proEtaleSheafAdjunction f (Type (t + 1))) I c.hom
    (proEtaleRingModulePullback f R S c)
    (fun N ↦ congrArg (fun F : C ⥤ D ↦
      SheafOfModules.changeOfRings.{t, t + 1, t + 1} c.hom (F.obj N)) hI.symm)
    (fun a ↦ hmap' _ hI a) P hP hflat).1

/-- The canonical derived comparison is uniquely fixed on K-flat representatives by the
strict ordinary comparison and the two universal derived counits. -/
theorem reductionPullIso_existsUnique :
    ∃! τ : reduction d V ⋙ exchangeConstantPull (A := A) f ≅
        pull (A := A) f ⋙ reduction d U,
      ReductionPullNormalized d f τ := by
  let M₀ : CochainComplex (reductionModules V (exchangeConstantRing V A)) ℤ → Prop :=
    fun K ↦ K.IsKFlatIndependentCoefficients ∧ ∀ n : ℤ,
      SheafOfModules.IsFlatOnSite (J := ProEt.topology V)
        (R := exchangeConstantRing V A) (K.X n)
  have hres (K : CochainComplex (reductionModules V (exchangeConstantRing V A)) ℤ) :
      ∃ (L : CochainComplex (reductionModules V (exchangeConstantRing V A)) ℤ) (s : L ⟶ K),
        M₀ L ∧ QuasiIso s := by
    exact flatKFlatResolution V (exchangeConstantRing V A) K
  exact modelPull_existsUnique (reductionModule d V) (reductionModule d U)
    (proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))
    (exchangeTowerModulePull f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))
    (reductionData d V) (reductionData d U) (ordinaryReductionPullIso d f)
    M₀ (fun _ h ↦ h.1) hres
    (fun K h ↦ pullback_kFlat f _ _ _ K h.1 h.2)

end DerivedPullComparison

/-- The normalized reduction-tower/pullback isomorphism, rather than an arbitrary lift
of levelwise maps. -/
def reductionPullIso :
    reduction d V ⋙ exchangeConstantPull (A := A) f ≅
      pull (A := A) f ⋙ reduction d U :=
  (reductionPullIso_existsUnique d f).choose

/-- The strict projection is the adjunct of reduction of the ambient counit. -/
def projection (K : D (A := A) U) :
    (reduction d V).obj ((push (A := A) f).obj K) ⟶
      (exchangeConstantPush (A := A) f).obj ((reduction d U).obj K) :=
  (exchangeTowerAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
    (exchangeConstantIso f A)).homEquiv _ _
      ((reductionPullIso d f).hom.app ((push (A := A) f).obj K) ≫
        (reduction d U).map ((proEtaleRingDerivedAdjunction f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).counit.app K))

end AlgebraicGeometry.Scheme.OrderedExchange
