/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionTower
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
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionModels
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import all WeilConjectures.CategoryTheory.FlatScalarTowerLimit.FlatScalarTowerLimitSquare
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullbackReflection
import WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitDerived
import WeilConjectures.AlgebraicGeometry.Derived.DerivedReductionAugmentationCompatibility

/-! # The balancing comparisons `rho` and `lambda` of the ordered completed exchange

This file constructs the strict and derived balancing comparisons `ordinaryRho`, `rho`,
`ordinaryLambda` and `lambda` with their universal normalizations. Their compatibility with
the completion units, and the comparison data built from them, are in
`WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData`.

## References

* Stacks Project, Tags 099M, 099N, 0A07 and 0E48
* Stacks 099M, 06YY
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange

-- Prefer the concrete pro-etale site and module instances to abstract corner projections.
attribute [local instance 0] SheafOfModules.RingedTensorCorner.category
  SheafOfModules.RingedTensorCorner.derived

private theorem orderedAbSheafify (T : Scheme.{t}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{t, 0} T

private theorem orderedAbLocallyBijective (T : Scheme.{t}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem orderedRestrictLimits (T : Scheme.{t})
    {R B : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ B) :
    PreservesLimitsOfShape ℕᵒᵖ (reductionRestrict T φ) := by
  let := orderedAbSheafify T
  let := orderedAbLocallyBijective T
  let r := reductionRestrict T φ
  let F := SheafOfModules.forget.{t + 1} (reductionModuleRing T R) ⋙
    PresheafOfModules.toPresheaf (reductionModuleRing T R).obj
  let e : SheafOfModules.forget.{t + 1} (reductionModuleRing T B) ⋙
      PresheafOfModules.toPresheaf (reductionModuleRing T B).obj ≅ r ⋙ F := Iso.refl _
  have : PreservesLimitsOfShape ℕᵒᵖ (r ⋙ F) :=
    preservesLimitsOfShape_of_natIso e
  have : ReflectsLimitsOfShape ℕᵒᵖ F := reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves r F

set_option backward.isDefEq.respectTransparency.types true in
private theorem uniqueLimitComparison {C E : Type*} [Category C] [Category E]
    [HasLimitsOfShape ℕᵒᵖ C] [HasLimitsOfShape ℕᵒᵖ E]
    (r : C ⥤ E) [PreservesLimitsOfShape ℕᵒᵖ r] :
    ∃! e : lim ⋙ r ≅ (Functor.whiskeringRight ℕᵒᵖ C E).obj r ⋙ lim,
      ∀ (Z : ℕᵒᵖ ⥤ C) (n : ℕ),
        e.hom.app Z ≫ limit.π (Z ⋙ r) (op n) = r.map (limit.π Z (op n)) := by
  refine ⟨preservesLimitNatIso (J := ℕᵒᵖ) r, ?_, ?_⟩
  · intro Z n
    exact preservesLimitIso_hom_π r Z (op n)
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext Z
    apply limit.hom_ext
    intro n
    exact (he Z n.unop).trans (preservesLimitIso_hom_π r Z n).symm

attribute [local irreducible] completedAdicChangeData completedAdicDerivedChange
  HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  completedAdicChange reductionChange reductionDerivedChange reductionHomotopy
  completedReductionTower reduction

attribute [local instance 3000] orderedAbSheafify orderedAbLocallyBijective
  reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory
  reductionRingModulesHasDerivedCategory

-- Normalize the two ordinary presentations of scalar restriction before matching complexes.
set_option allowUnsafeReducibility true in
attribute [local reducible] reductionRestrict completedReductionComplexTowerFunctor

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

private theorem orderedScalarFlat (T : Scheme.{t}) :
    SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      ((SheafOfModules.restrictScalars ((adicLisseForget T).map (exchangeScalar d T))).obj
        (SheafOfModules.unit ((adicLisseForget T).obj (d.completedRing T)))) := by
  let := d.noetherian
  have hc : ∀ n : ℕ, exchangeScalar d T ≫ (pbcCompletedComparison T d).inv ≫
      limit.π (adicLisseRingSystem T d.ideal) (op n) =
        (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) := by
    intro n
    dsimp only [exchangeScalar]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (adicDatumScalar_exists T
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite }).exists.choose_spec n
  exact (completed_constant_algebra_flat_quotients T d.ideal _
    (pbcCompletedComparison T d) (exchangeScalar d T) hc).1

theorem exchangeScalar_comp_projection (T : Scheme.{t}) (n : ℕ) :
    exchangeScalar d T ≫ (pbcCompletedComparison T d).inv ≫
      limit.π (adicLisseRingSystem T d.ideal) (op n) =
        (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) := by
  dsimp only [exchangeScalar]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (adicDatumScalar_exists T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite }).exists.choose_spec n

theorem projection_eq_comparison (T : Scheme.{t}) (n : ℕ) :
    d.projection T n = (pbcCompletedComparison T d).inv ≫
      limit.π (adicLisseRingSystem T d.ideal) (op n) ≫
        (pbcLevelConstantComparison T d n).hom := by
  have h := HasLimit.isoOfNatIso_inv_π (pbcConstantSystemComparison T d) (op n)
  unfold pbcCompletedComparison
  rw [reassoc_of% h]
  simp [pbcConstantSystemComparison, completedReductionProjection, reductionCoefficientSystem]

theorem quotient_eq_constant (T : Scheme.{t}) (n : ℕ) :
    quotient d T n = (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
      (pbcLevelConstantComparison T d n).hom := by
  unfold quotient
  rw [projection_eq_comparison, ← exchangeScalar_comp_projection]
  simp only [Category.assoc]

theorem quotient_surjective (T : Scheme.{t}) (n : ℕ) (U : T.ProEtᵒᵖ) :
    Function.Surjective ((quotient d T n).hom.app U) := by
  let := d.noetherian
  rw [quotient_eq_constant]
  let V : (CompletedConstantAlgebra.smallSite T)ᵒᵖ := op (AsSmall.up.obj U.unop)
  have hs := (ConstantCompletion.flat_and_quotients_quotient
    (CompletedConstantAlgebra.smallTopology T) A d.ideal n (AsSmall.up.obj U.unop)).1
  let iA := (CompletedConstantAlgebra.constantsIso T).app (CommRingCat.of A)
  let iQ := (CompletedConstantAlgebra.constantsIso T).app
    (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))
  have hn := (CompletedConstantAlgebra.constantsIso T).hom.naturality
    (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))
  let dd := pbcLevelConstantComparison T d n
  intro y
  obtain ⟨x, hx⟩ := hs (iQ.hom.hom.app V (dd.inv.hom.app U y))
  refine ⟨iA.inv.hom.app V x, ?_⟩
  have h1 := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app V) hn)
    (iA.inv.hom.app V x)
  have hA : iA.hom.hom.app V (iA.inv.hom.app V x) = x :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app V) iA.inv_hom_id) x
  have hQ (z : _) : iQ.inv.hom.app V (iQ.hom.hom.app V z) = z :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app V) iQ.hom_inv_id) z
  have hd : dd.hom.hom.app U (dd.inv.hom.app U y) = y :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U) dd.inv_hom_id) y
  change iQ.hom.hom.app V (((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))).hom.app U
        (iA.inv.hom.app V x)) =
    ((ConstantCompletion.quotient (CompletedConstantAlgebra.smallTopology T) A d.ideal n).hom.app V)
      (iA.hom.hom.app V (iA.inv.hom.app V x)) at h1
  rw [hA, hx] at h1
  have h2 := congrArg (iQ.inv.hom.app V) h1
  rw [hQ, hQ] at h2
  change dd.hom.hom.app U _ = y
  exact (congrArg (dd.hom.hom.app U) h2).trans hd

theorem projection_ker_le (T : Scheme.{t}) (n : ℕ) (U : T.ProEtᵒᵖ)
    (b : (d.completedRing T).obj.obj U) (hb : (d.projection T n).hom.app U b = 0) :
    b ∈ Ideal.span (Set.range (fun a : ↥(d.ideal ^ (n + 1)) ↦
      (exchangeScalar d T).hom.app U ((adicLisseConstantUnit T A).app U (a : A)))) := by
  let := d.noetherian
  let J := Ideal.span (Set.range (fun a : ↥(d.ideal ^ (n + 1)) ↦
      (exchangeScalar d T).hom.app U ((adicLisseConstantUnit T A).app U (a : A))))
  have h := (CompletedConstantAlgebra.projection_surjective_and_kernel T d.ideal
    (S := d.completedRing T)
    (pbcCompletedComparison T d) (exchangeScalar d T)
    (exchangeScalar_comp_projection d T) n (pbcLevelConstantComparison T d n)
    (d.projection T n) (projection_eq_comparison d T n) U).2
    ((d.completedRing T).obj.obj U ⧸ J) J.mkQ
    (fun a ↦ (Submodule.Quotient.mk_eq_zero J).2 (Ideal.subset_span ⟨a, rfl⟩)) b hb
  exact (Submodule.Quotient.mk_eq_zero J).1 h

theorem quotient_unit_eq_zero (T : Scheme.{t}) (n : ℕ) (U : T.ProEtᵒᵖ) (a : A)
    (ha : a ∈ d.ideal ^ (n + 1)) :
    (quotient d T n).hom.app U ((adicLisseConstantUnit T A).app U a) = 0 := by
  rw [quotient_eq_constant]
  have hn := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app U)
    (toSheafify_naturality (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))))) a
  change (adicLisseConstantUnit T (A ⧸ d.ideal ^ (n + 1))).app U
      (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a) =
    (((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))).hom.app U
        ((adicLisseConstantUnit T A).app U a)) at hn
  change (pbcLevelConstantComparison T d n).hom.hom.app U
    (((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))).hom.app U
        ((adicLisseConstantUnit T A).app U a)) = 0
  rw [← hn, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero, map_zero]

/-- Maps out of a scalar extension given by an ordinary linear map, with the pure-tensor
formula. -/
theorem changeLift_exists (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (N : reductionModules X R) (Y : reductionModules X S)
    (v : N ⟶ (reductionRestrict X φ).obj Y) :
    ∃ F : (reductionChange X φ).obj N ⟶ Y, ∀ (U : X.ProEtᵒᵖ) (s : S.obj.obj U)
      (x : N.val.obj U),
      F.val.app U (reductionTensorSection X φ N U s x) =
        s • (show Y.val.obj U from v.val.app U x) := by
  let adj := (ordinaryAdjunction_exists X φ).choose
  let F := (adj.homEquiv N Y).symm v
  refine ⟨F, ?_⟩
  intro U s x
  have hb : F.val.app U (reductionTensorSection X φ N U 1 x) = v.val.app U x := by
    have hh := (ordinaryAdjunction_exists X φ).choose_spec N Y F U x
    rw [Equiv.apply_symm_apply] at hh
    exact (eq_of_heq hh).symm
  have ht := tensorSection_smul X φ N U s 1 x
  rw [mul_one] at ht
  rw [← ht, map_smul, hb]

/-- Maps out of a scalar extension are determined on sheafified pure tensors. -/
theorem change_hom_ext (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (N : reductionModules X R) (Y : reductionModules X S)
    (f g : (reductionChange X φ).obj N ⟶ Y)
    (h : ∀ (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U),
      f.val.app U (reductionTensorSection X φ N U s x) =
        g.val.app U (reductionTensorSection X φ N U s x)) : f = g := by
  have h' := level_hom_ext X φ N ((reductionRestrict X φ).obj Y)
    ((reductionRestrict X φ).map f) ((reductionRestrict X φ).map g) h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  exact congrArg (fun k ↦ k.val.app U y) h'

/-- On the constant-coefficient restriction of a completed module, the quotient unit is
linear over the completed ring through its finite projection. -/
theorem quotientUnit_smul (T : Scheme.{t}) (n : ℕ)
    (M : reductionModules T (d.completedRing T)) (U : T.ProEtᵒᵖ)
    (r : (d.completedRing T).obj.obj U) (x : M.val.obj U) :
    reductionTensorSection T (quotient d T n)
        ((reductionRestrict T (exchangeScalar d T)).obj M) U 1 (r • x) =
      reductionTensorSection T (quotient d T n)
        ((reductionRestrict T (exchangeScalar d T)).obj M) U
          ((d.projection T n).hom.app U r) x := by
  let N := (reductionRestrict T (exchangeScalar d T)).obj M
  let q := quotient d T n
  let u := reductionUnit T q N
  have hu (y : M.val.obj U) : u.val.app U y = reductionTensorSection T q N U 1 y :=
    reductionUnit_apply T q N U y
  have hlin (a : (exchangeConstantRing T A).obj.obj U) (y : M.val.obj U) :
      reductionTensorSection T q N U 1 ((exchangeScalar d T).hom.app U a • y) =
        reductionTensorSection T q N U (q.hom.app U a) y := by
    have h := (u.val.app U).hom.map_smul a y
    change u.val.app U ((exchangeScalar d T).hom.app U a • y) =
      q.hom.app U a • (show ((reductionChange T q).obj N).val.obj U from u.val.app U y) at h
    rw [hu, hu, tensorSection_smul, mul_one] at h
    exact h
  have hadd (y z : M.val.obj U) :
      reductionTensorSection T q N U 1 (y + z) =
        reductionTensorSection T q N U 1 y + reductionTensorSection T q N U 1 z := by
    rw [← hu, ← hu, ← hu]
    exact map_add (u.val.app U).hom y z
  have hzero : reductionTensorSection T q N U 1 (0 : M.val.obj U) = 0 := by
    rw [← hu]
    exact map_zero (u.val.app U).hom
  have hspan (b : (d.completedRing T).obj.obj U)
      (hb : b ∈ Ideal.span (Set.range (fun a : ↥(d.ideal ^ (n + 1)) ↦
        (exchangeScalar d T).hom.app U ((adicLisseConstantUnit T A).app U (a : A))))) :
      ∀ y : M.val.obj U, reductionTensorSection T q N U 1 (b • y) = 0 := by
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨a, rfl⟩ := hb
      intro y
      rw [hlin, quotient_unit_eq_zero d T n U a a.property]
      have h0 := tensorSection_smul T q N U 0 1 y
      rw [zero_mul, zero_smul] at h0
      exact h0.symm
    | zero =>
      intro y
      rw [zero_smul, hzero]
    | add b b' _ _ hb hb' =>
      intro y
      rw [add_smul, hadd, hb, hb', add_zero]
    | smul a b _ hb =>
      intro y
      rw [smul_eq_mul, mul_comm, mul_smul, hb]
  obtain ⟨a, ha⟩ := quotient_surjective d T n U ((d.projection T n).hom.app U r)
  have hk : (d.projection T n).hom.app U (r - (exchangeScalar d T).hom.app U a) = 0 := by
    rw [map_sub, ← ha]
    exact sub_self _
  have hr : r • x = (exchangeScalar d T).hom.app U a • x +
      (r - (exchangeScalar d T).hom.app U a) • x := by
    rw [← add_smul, add_sub_cancel]
  rw [hr, hadd, hspan _ (projection_ker_le d T n U _ hk), add_zero, hlin, ← ha]

/-- The finite-level balancing isomorphism `(A/I^{n+1}) ⊗_A M ≅ (Â/I^{n+1}Â) ⊗_Â M`. -/
theorem ordinaryRhoLevel_exists (T : Scheme.{t}) (n : ℕ)
    (M : reductionModules T (d.completedRing T)) :
    ∃ i : (reductionChange T (quotient d T n)).obj
          ((reductionRestrict T (exchangeScalar d T)).obj M) ≅
        (reductionChange T (d.projection T n)).obj M,
      ∀ (U : T.ProEtᵒᵖ) (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U),
        i.hom.val.app U (reductionTensorSection T (quotient d T n)
          ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) =
            reductionTensorSection T (d.projection T n) M U s x := by
  let N := (reductionRestrict T (exchangeScalar d T)).obj M
  let q := quotient d T n
  let p := d.projection T n
  let v : N ⟶ (reductionRestrict T q).obj ((reductionChange T p).obj M) :=
    (reductionRestrict T (exchangeScalar d T)).map (reductionUnit T p M)
  obtain ⟨F, hF⟩ := changeLift_exists T q N ((reductionChange T p).obj M) v
  let ua := (PresheafOfModules.toPresheaf (reductionModuleRing T
    (exchangeConstantRing T A)).obj).map (reductionUnit T q N).val
  let w : M ⟶ (reductionRestrict T p).obj ((reductionChange T q).obj N) :=
    ⟨PresheafOfModules.homMk ua (by
      intro U r x
      change (reductionUnit T q N).val.app U (r • x) =
        p.hom.app U r •
          (show ((reductionChange T q).obj N).val.obj U from
            (reductionUnit T q N).val.app U x)
      rw [reductionUnit_apply, reductionUnit_apply, tensorSection_smul, mul_one]
      exact quotientUnit_smul d T n M U r x)⟩
  obtain ⟨G, hG⟩ := changeLift_exists T p M ((reductionChange T q).obj N) w
  have hF' (U : T.ProEtᵒᵖ) (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U) :
      F.val.app U (reductionTensorSection T q N U s x) =
        reductionTensorSection T p M U s x := by
    rw [hF]
    erw [reductionUnit_apply]
    exact (tensorSection_smul T p M U s 1 x).trans (by rw [mul_one])
  have hG' (U : T.ProEtᵒᵖ) (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U) :
      G.val.app U (reductionTensorSection T p M U s x) =
        reductionTensorSection T q N U s x := by
    rw [hG]
    erw [reductionUnit_apply]
    exact (tensorSection_smul T q N U s 1 x).trans (by rw [mul_one])
  refine ⟨⟨F, G, ?_, ?_⟩, hF'⟩
  · apply change_hom_ext T q N
    intro U s x
    change G.val.app U (F.val.app U _) = _
    rw [hF', hG']
    rfl
  · apply change_hom_ext T p M
    intro U s x
    change F.val.app U (G.val.app U _) = _
    rw [hG', hF']
    rfl

/-- The chosen finite-level balancing isomorphism. -/
def ordinaryRhoLevel (T : Scheme.{t}) (n : ℕ) (M : reductionModules T (d.completedRing T)) :
    (reductionChange T (quotient d T n)).obj
          ((reductionRestrict T (exchangeScalar d T)).obj M) ≅
        (reductionChange T (d.projection T n)).obj M :=
  (ordinaryRhoLevel_exists d T n M).choose

theorem ordinaryRhoLevel_hom_apply (T : Scheme.{t}) (n : ℕ)
    (M : reductionModules T (d.completedRing T)) (U : T.ProEtᵒᵖ)
    (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U) :
    (ordinaryRhoLevel d T n M).hom.val.app U (reductionTensorSection T (quotient d T n)
      ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) =
        reductionTensorSection T (d.projection T n) M U s x :=
  (ordinaryRhoLevel_exists d T n M).choose_spec U s x

/-- Existence of the normalized ordinary strict balancing comparison.
The finite quotient tensor comparisons are assembled into a morphism of strict
towers; the section formula is preserved by the quotient transition maps and
the completed coefficient projections. -/
theorem ordinaryRho_exists (T : Scheme.{t}) :
    ∃ e : reductionRestrict T (exchangeScalar d T) ⋙ reductionModule d T ≅
        completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T,
      ∀ (M : reductionModules T (d.completedRing T)) (n : ℕ) (U : T.ProEtᵒᵖ)
        (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U),
        ((e.hom.app M).app (op n)).val.app U
            (reductionTensorSection T (quotient d T n)
              ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) =
          reductionTensorSection T (d.projection T n) M U s x := by
  let c := exchangeScalar d T
  let r (M : reductionModules T (d.completedRing T)) (n : ℕ) :
      ((reductionRestrict T c ⋙ reductionModule d T).obj M).obj (op n) ⟶
        ((completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T).obj M).obj
          (op n) :=
    (reductionRestrict T (quotient d T n)).map (ordinaryRhoLevel d T n M).hom
  have hr (M : reductionModules T (d.completedRing T)) (n : ℕ) (U : T.ProEtᵒᵖ)
      (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U) :
      (r M n).val.app U (reductionTensorSection T (quotient d T n)
        ((reductionRestrict T c).obj M) U s x) =
          reductionTensorSection T (d.projection T n) M U s x :=
    ordinaryRhoLevel_hom_apply d T n M U s x
  let φ (M : reductionModules T (d.completedRing T)) :
      (reductionRestrict T c ⋙ reductionModule d T).obj M ⟶
        (completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T).obj M :=
    NatTrans.ofOpSequence (fun n ↦ r M n) (by
      intro n
      have h1 : ((reductionRestrict T c ⋙ reductionModule d T).obj M).map
          (homOfLE (Nat.le_succ n)).op = (step d T n).app ((reductionRestrict T c).obj M) := by
        simp [reductionModule]
      have h2 : ((completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T).obj
          M).map (homOfLE (Nat.le_succ n)).op = (proEtaleRingRestrictScalars c).map
            ((completedReductionTransition T d (n + 1) n (Nat.le_succ n)).app M) := by
        simp [completedReductionModuleTowerFunctor, completedReductionModuleTower]
        rfl
      rw [h1, h2]
      apply level_hom_ext T (quotient d T (n + 1)) ((reductionRestrict T c).obj M)
      intro U s x
      simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
      change (r M n).val.app U (((step d T n).app ((reductionRestrict T c).obj M)).val.app U
          (reductionTensorSection T (quotient d T (n + 1))
            ((reductionRestrict T c).obj M) U s x)) =
        ((completedReductionTransition T d (n + 1) n (Nat.le_succ n)).app M).val.app U
          ((r M (n + 1)).val.app U (reductionTensorSection T (quotient d T (n + 1))
            ((reductionRestrict T c).obj M) U s x))
      have hs : ((step d T n).app ((reductionRestrict T c).obj M)).val.app U
          (reductionTensorSection T (quotient d T (n + 1)) ((reductionRestrict T c).obj M) U s x) =
            reductionTensorSection T (quotient d T n) ((reductionRestrict T c).obj M) U
              ((reductionCoefficientMap T d (n + 1) n (Nat.le_succ n)).hom.app U s) x :=
        (step_existsUnique d T n).exists.choose_spec _ U s x
      rw [hs, hr, hr]
      exact ((completedReductionTransition_exists T d (n + 1) n
        (Nat.le_succ n)).exists.choose_spec M U s x).symm)
  have hφ (M : reductionModules T (d.completedRing T)) : IsIso (φ M) := by
    have (n : ℕᵒᵖ) : IsIso ((φ M).app n) := by
      change IsIso ((reductionRestrict T (quotient d T n.unop)).map
        (ordinaryRhoLevel d T n.unop M).hom)
      infer_instance
    exact NatIso.isIso_of_isIso_app (φ M)
  refine ⟨NatIso.ofComponents (fun M ↦ asIso (φ M)) ?_, ?_⟩
  · intro M M' f
    apply NatTrans.ext
    funext n
    apply level_hom_ext T (quotient d T n.unop) ((reductionRestrict T c).obj M)
    intro U s x
    change (r M' n.unop).val.app U
        (((level d T n.unop).map ((reductionRestrict T c).map f)).val.app U
          (reductionTensorSection T (quotient d T n.unop)
            ((reductionRestrict T c).obj M) U s x)) =
        ((completedReductionLevel T d n.unop).map f).val.app U
          ((r M n.unop).val.app U (reductionTensorSection T (quotient d T n.unop)
            ((reductionRestrict T c).obj M) U s x))
    rw [tensorSection_map, hr, hr]
    exact (reductionTensor_map T (d.projection T n.unop) f U s x).symm
  · intro M n U s x
    exact hr M n U s x

/-- Uniqueness of the normalized ordinary strict balancing comparison.
The quotient tensor sections generate each finite reduction, so two tower
isomorphisms satisfying the displayed section formula agree at every level and
therefore agree as natural transformations. -/
theorem ordinaryRho_unique (T : Scheme.{t})
    {e₁ e₂ : reductionRestrict T (exchangeScalar d T) ⋙ reductionModule d T ≅
        completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T}
    (h₁ : ∀ (M : reductionModules T (d.completedRing T)) (n : ℕ) (U : T.ProEtᵒᵖ)
      (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U),
      ((e₁.hom.app M).app (op n)).val.app U
          (reductionTensorSection T (quotient d T n)
            ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) =
        reductionTensorSection T (d.projection T n) M U s x)
    (h₂ : ∀ (M : reductionModules T (d.completedRing T)) (n : ℕ) (U : T.ProEtᵒᵖ)
      (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U),
      ((e₂.hom.app M).app (op n)).val.app U
          (reductionTensorSection T (quotient d T n)
            ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) =
        reductionTensorSection T (d.projection T n) M U s x) :
    e₁ = e₂ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  apply level_hom_ext T (quotient d T n.unop)
    ((reductionRestrict T (exchangeScalar d T)).obj M)
  intro U s x
  exact (h₁ M n.unop U s x).trans (h₂ M n.unop U s x).symm

/-- Derived restriction along the existing compatible-residue coefficient map. -/
abbrev res (T : Scheme.{t}) := reductionDerivedRestrict T (exchangeScalar d T)

/-- The canonical balancing isomorphism on the single ordinary strict quotient diagram. -/
theorem ordinaryRho_existsUnique (T : Scheme.{t}) :
    ∃! e : reductionRestrict T (exchangeScalar d T) ⋙ reductionModule d T ≅
        completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T,
      ∀ (M : reductionModules T (d.completedRing T)) (n : ℕ) (U : T.ProEtᵒᵖ)
        (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U),
        ((e.hom.app M).app (op n)).val.app U
            (reductionTensorSection T (quotient d T n)
              ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) =
          reductionTensorSection T (d.projection T n) M U s x := by
  obtain ⟨e, he⟩ := ordinaryRho_exists d T
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact (ordinaryRho_unique d T he he').symm

/-- Ordinary strict balancing, with its prescribed tensor normalization. -/
def ordinaryRho (T : Scheme.{t}) :
    reductionRestrict T (exchangeScalar d T) ⋙ reductionModule d T ≅
      completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T :=
  (ordinaryRho_existsUnique d T).exists.choose

attribute [local irreducible] ordinaryRho reductionModule completedReductionModuleTowerFunctor
  completedReductionCoefficient constantSheaf AdicCoefficients.coefficientRing
  SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The complex-level normalization of the specified rho comparison. -/
def RhoNormalization (T : Scheme.{t})
    (e : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T) : Prop :=
  ∀ P : CochainComplex (reductionModules T (d.completedRing T)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
          (R := d.completedRing T) P →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
          (R := d.completedRing T) (P.X n)) →
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (reduction d T).map
              ((reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app P) ≫
            reductionComplexCounit d T
              (((reductionRestrict T (exchangeScalar d T)).mapHomologicalComplex (.up ℤ)).obj P) =
          (exchangeTowerRes d T).map (completedReductionTowerComplexCounit T d P) ≫
            (exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app
              ((completedReductionComplexTowerFunctor T d).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryRho d T).symm (.up ℤ)).hom.app P)

attribute [local irreducible] RhoNormalization
/-- The complex-level counit of a derived functor equipped with a homotopy-level counit,
as a natural transformation. -/
def complexCounitNatTrans
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (E : B ⥤ C) [E.Additive] (L : DerivedCategory B ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ L ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso B).inv L ≫
    Functor.whiskerLeft (HomotopyCategory.quotient B (.up ℤ)) ε ≫
    Functor.whiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft (E.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso C).hom

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- A functor with a complex-level comparison to an additive functor, invertible on a
resolving class, is isomorphic to the chosen left derived model, compatibly with the
complex counits. -/
theorem _root_.AlgebraicGeometry.Scheme.DerivedReductionModelData.exists_iso_of_complexCounit
    {B C : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    [Category C] [Abelian C] [HasDerivedCategory C]
    {E : B ⥤ C} [E.Additive] {S : CochainComplex B ℤ → Prop}
    (D : DerivedReductionModelData E S)
    (hres : ∀ K : CochainComplex B ℤ, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K),
      S L ∧ QuasiIso s)
    (G : DerivedCategory B ⥤ DerivedCategory C)
    (α : DerivedCategory.Q ⋙ G ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hα : ∀ K, S K → IsIso (α.app K)) :
    ∃ β : G ≅ D.reduction, ∀ K : CochainComplex B ℤ,
      β.hom.app (DerivedCategory.Q.obj K) ≫ D.complexCounit K = α.app K := by
  let W := HomotopyCategory.quasiIso B (.up ℤ)
  let : D.reduction.IsLeftDerivedFunctor D.counit W := D.isLeftDerived
  let τ : HomotopyCategory.quotient B (.up ℤ) ⋙ (DerivedCategory.Qh ⋙ G) ⟶
      HomotopyCategory.quotient B (.up ℤ) ⋙
        (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso B).hom G ≫ α ≫
      Functor.whiskerLeft (E.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso C).inv ≫
      Functor.whiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh
  let αh : DerivedCategory.Qh ⋙ G ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    Quotient.natTransLift _ τ
  let β := D.reduction.leftDerivedLift D.counit W G αh
  have hβ (K : CochainComplex B ℤ) :
      β.app (DerivedCategory.Q.obj K) ≫ D.complexCounit K = α.app K := by
    have hf := D.reduction.leftDerived_fac_app D.counit W G αh
      ((HomotopyCategory.quotient B (.up ℤ)).obj K)
    have hF : (E.mapHomotopyCategoryFactors (.up ℤ)).hom.app K =
        𝟙 ((HomotopyCategory.quotient C (.up ℤ)).obj
          ((E.mapHomologicalComplex (.up ℤ)).obj K)) := rfl
    have hτ : αh.app ((HomotopyCategory.quotient B (.up ℤ)).obj K) =
        G.map ((DerivedCategory.quotientCompQhIso B).hom.app K) ≫ α.app K ≫
          (DerivedCategory.quotientCompQhIso C).inv.app
            ((E.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((E.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) := rfl
    have hf' : β.app ((HomotopyCategory.quotient B (.up ℤ) ⋙ DerivedCategory.Qh).obj K) ≫
        D.counit.app ((HomotopyCategory.quotient B (.up ℤ)).obj K) =
        G.map ((DerivedCategory.quotientCompQhIso B).hom.app K) ≫ α.app K ≫
          (DerivedCategory.quotientCompQhIso C).inv.app
            ((E.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((E.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) :=
      hf.trans hτ
    have hF' : DerivedCategory.Qh.map ((E.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) =
        𝟙 _ :=
      (congrArg DerivedCategory.Qh.map hF).trans (DerivedCategory.Qh.map_id _)
    unfold DerivedReductionModelData.complexCounit
    rw [hF']
    erw [Category.id_comp]
    erw [hF', Category.comp_id] at hf'
    rw [← β.naturality_assoc]
    erw [reassoc_of% hf']
    erw [Iso.inv_hom_id_app, Category.comp_id]
    rw [← G.map_comp_assoc, Iso.inv_hom_id_app, G.map_id, Category.id_comp]
  have hiso (Y : DerivedCategory B) : IsIso (β.app Y) := by
    obtain ⟨L, s, hL, hs⟩ := hres (DerivedCategory.Q.objPreimage Y)
    let eY : DerivedCategory.Q.obj L ≅ Y :=
      asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso Y
    have : IsIso (D.complexCounit L) := D.complexCounit_isIso L hL
    have : IsIso (α.app L) := hα L hL
    have : IsIso (β.app (DerivedCategory.Q.obj L)) := by
      have h : β.app (DerivedCategory.Q.obj L) = α.app L ≫ inv (D.complexCounit L) := by
        rw [← hβ L, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [h]
      infer_instance
    have : IsIso (G.map eY.hom ≫ β.app Y) := by
      rw [β.naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left (G.map eY.hom) (β.app Y)
  have : IsIso β := NatIso.isIso_of_isIso_app β
  exact ⟨asIso β, hβ⟩

section RhoCounits

attribute [local semireducible] reduction

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The complex counit of the strict-tower side of `rho`, followed by exact restriction. -/
private def rhoTowerCounit (T : Scheme.{t}) :
    DerivedCategory.Q ⋙ (completedReductionTower T d ⋙ exchangeTowerRes d T) ⟶
      (completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (complexCounitNatTrans (completedReductionModuleTowerFunctor T d)
      (completedReductionTower T d) (coherenceReductionTowerCounit T d))
      (exchangeTowerRes d T) ≫
    Functor.whiskerLeft
      ((completedReductionModuleTowerFunctor T d).mapHomologicalComplex (.up ℤ))
      (exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The complex counit of the ordinary side of `rho`: exact restriction, the ordinary
reduction counit and `ordinaryRho`. -/
private def rhoOrdinaryCounit (T : Scheme.{t}) :
    DerivedCategory.Q ⋙ (res d T ⋙ reduction d T) ⟶
      (completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom
      (reduction d T) ≫
    Functor.whiskerLeft
      ((reductionRestrict T (exchangeScalar d T)).mapHomologicalComplex (.up ℤ))
      (complexCounitNatTrans (reductionModule d T) (reduction d T)
        (reductionData d T).counit) ≫
    Functor.whiskerRight (NatIso.mapHomologicalComplex (ordinaryRho d T) (.up ℤ)).hom
      DerivedCategory.Q

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem rhoTowerCounit_app (T : Scheme.{t})
    (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ) :
    (rhoTowerCounit d T).app P =
      (exchangeTowerRes d T).map (completedReductionTowerComplexCounit T d P) ≫
        (exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app
          ((completedReductionComplexTowerFunctor T d).obj P) :=
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem rhoOrdinaryCounit_app (T : Scheme.{t})
    (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ) :
    (rhoOrdinaryCounit d T).app P =
      (reduction d T).map
          ((reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app P) ≫
        reductionComplexCounit d T
          (((reductionRestrict T (exchangeScalar d T)).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryRho d T) (.up ℤ)).hom.app P) :=
  rfl

end RhoCounits

attribute [local semireducible] reduction in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The derived strict-tower comparison is fixed on K-flat representatives before evaluation. -/
theorem rho_exists (T : Scheme.{t}) :
    ∃ e : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T, RhoNormalization d T e := by
  have hflat := orderedScalarFlat d T
  let c := exchangeScalar d T
  let E := completedReductionModuleTowerFunctor T d ⋙ exchangeTowerModuleRes d T
  let S : CochainComplex (reductionModules T (d.completedRing T)) ℤ → Prop := fun P ↦
    CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
        (R := d.completedRing T) P ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
        (R := d.completedRing T) (P.X n)
  have hres (K : CochainComplex (reductionModules T (d.completedRing T)) ℤ) :
      ∃ (L : CochainComplex (reductionModules T (d.completedRing T)) ℤ) (s : L ⟶ K),
        S L ∧ QuasiIso s :=
    flatKFlatResolution T (d.completedRing T) K
  let α₁ : DerivedCategory.Q ⋙ (completedReductionTower T d ⋙ exchangeTowerRes d T) ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := rhoTowerCounit d T
  let α₂ : DerivedCategory.Q ⋙ (res d T ⋙ reduction d T) ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := rhoOrdinaryCounit d T
  have hα₁ (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ) :
      α₁.app P = (exchangeTowerRes d T).map (completedReductionTowerComplexCounit T d P) ≫
        (exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app
          ((completedReductionComplexTowerFunctor T d).obj P) := rhoTowerCounit_app d T P
  have hα₂ (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ) :
      α₂.app P = (reduction d T).map
          ((reductionRestrict T c).mapDerivedCategoryFactors.hom.app P) ≫
        reductionComplexCounit d T
          (((reductionRestrict T c).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryRho d T) (.up ℤ)).hom.app P) :=
    rhoOrdinaryCounit_app d T P
  have hiso₁ (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ) (hP : S P) :
      IsIso (α₁.app P) := by
    have h := (completedReductionTower_properties T d).2.2 P hP.1
    have : IsIso (completedReductionTowerComplexCounit T d P) := by
      unfold completedReductionTowerComplexCounit Scheme.reductionComplexCounit
      exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h inferInstance)
    rw [hα₁]
    exact IsIso.comp_isIso' inferInstance (Iso.isIso_hom
      ((exchangeTowerModuleRes d T).mapDerivedCategoryFactors.app
        ((completedReductionComplexTowerFunctor T d).obj P)))
  have hiso₂ (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ) (hP : S P) :
      IsIso (α₂.app P) := by
    have hr := SheafOfModules.isKFlat_restrictScalars_of_flat c hflat P hP.1
    have hi := (reductionData d T).complexCounit_isIso
      (((reductionRestrict T c).mapHomologicalComplex (.up ℤ)).obj P) hr.1
    have hi' : IsIso (reductionComplexCounit d T
        (((reductionRestrict T c).mapHomologicalComplex (.up ℤ)).obj P)) := by
      simpa only [reductionComplexCounit, reduction] using hi
    rw [hα₂]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hi' (Iso.isIso_hom
      (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex (ordinaryRho d T) (.up ℤ)).app P))))
  have hinv {K L : CochainComplex (reductionModules T (d.completedRing T)) ℤ}
      (s : K ⟶ L) (hK : S K) (hL : S L) (hs : QuasiIso s) :
      QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map s) := by
    have := hiso₁ K hK
    have := hiso₁ L hL
    have hn := α₁.naturality s
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    have h : DerivedCategory.Q.map ((E.mapHomologicalComplex (.up ℤ)).map s) =
        inv (α₁.app K) ≫ (completedReductionTower T d ⋙ exchangeTowerRes d T).map
          (DerivedCategory.Q.map s) ≫ α₁.app L := by
      rw [IsIso.eq_inv_comp]
      exact hn.symm
    rw [h]
    infer_instance
  let D := Classical.choice (leftDerivedModels E S hres hinv)
  obtain ⟨β₁, hβ₁⟩ := D.exists_iso_of_complexCounit hres _ α₁ hiso₁
  obtain ⟨β₂, hβ₂⟩ := D.exists_iso_of_complexCounit hres _ α₂ hiso₂
  refine ⟨β₁ ≪≫ β₂.symm, ?_⟩
  unfold RhoNormalization
  intro P _ _
  have key : (β₁ ≪≫ β₂.symm).hom.app (DerivedCategory.Q.obj P) ≫ α₂.app P = α₁.app P := by
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    rw [← hβ₂ P, Iso.inv_hom_id_app_assoc, hβ₁ P]
  rw [hα₁, hα₂] at key
  have hρ : DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (ordinaryRho d T) (.up ℤ)).hom.app P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (ordinaryRho d T).symm (.up ℤ)).hom.app P) = 𝟙 _ := by
    rw [← Functor.map_comp]
    have h : (NatIso.mapHomologicalComplex (ordinaryRho d T) (.up ℤ)).hom.app P ≫
        (NatIso.mapHomologicalComplex (ordinaryRho d T).symm (.up ℤ)).hom.app P = 𝟙 _ :=
      (NatIso.mapHomologicalComplex (ordinaryRho d T) (.up ℤ)).hom_inv_id_app P
    rw [h, CategoryTheory.Functor.map_id]
  have key' := key =≫ DerivedCategory.Q.map
    ((NatIso.mapHomologicalComplex (ordinaryRho d T).symm (.up ℤ)).hom.app P)
  simp only [Category.assoc] at key'
  erw [hρ, Category.comp_id] at key'
  exact key'

theorem rho_unique (T : Scheme.{t})
    {e₁ e₂ : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T}
    (h₁ : RhoNormalization d T e₁) (h₂ : RhoNormalization d T e₂) : e₁ = e₂ := by
  have hflat := orderedScalarFlat d T
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (reductionModules T (d.completedRing T)) (.up ℤ))
  intro P
  obtain ⟨L, f, ⟨hL, hLf⟩, hf⟩ := flatKFlatResolution T (d.completedRing T) P
  have := hf
  apply (cancel_epi
    ((completedReductionTower T d ⋙ exchangeTowerRes d T).map
      (DerivedCategory.Q.map f))).mp
  rw [e₁.hom.naturality, e₂.hom.naturality]
  suffices e₁.hom.app (DerivedCategory.Q.obj L) =
      e₂.hom.app (DerivedCategory.Q.obj L) by rw [this]
  have hr := SheafOfModules.isKFlat_restrictScalars_of_flat
    (exchangeScalar d T) hflat L hL
  have hi := (reductionData d T).complexCounit_isIso
    (((reductionRestrict T (exchangeScalar d T)).mapHomologicalComplex (.up ℤ)).obj L) hr.1
  have hi' : IsIso (reductionComplexCounit d T
      (((reductionRestrict T (exchangeScalar d T)).mapHomologicalComplex (.up ℤ)).obj L)) := by
    simpa only [reductionComplexCounit, reduction] using hi
  apply (cancel_mono
    ((reduction d T).map
      ((reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app L) ≫
      reductionComplexCounit d T
        (((reductionRestrict T (exchangeScalar d T)).mapHomologicalComplex (.up ℤ)).obj L))).mp
  unfold RhoNormalization at h₁ h₂
  exact (h₁ L hL hLf).trans (h₂ L hL hLf).symm

theorem rho_existsUnique (T : Scheme.{t}) :
    ∃! e : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T,
      RhoNormalization d T e := by
  obtain ⟨e, he⟩ := rho_exists d T
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact (rho_unique d T he he').symm

/-- The specified comparison rho, natural on all ambient inputs. -/
def rho (T : Scheme.{t}) :
    completedReductionTower T d ⋙ exchangeTowerRes d T ≅ res d T ⋙ reduction d T :=
  (rho_existsUnique d T).exists.choose

/-- The actual ordinary limit/scalar comparison, fixed by all its projections. -/
theorem ordinaryLambda_existsUnique (T : Scheme.{t}) :
    ∃! e : completedTowerLimit T (d.completedRing T) ⋙
          reductionRestrict T (exchangeScalar d T) ≅
        exchangeTowerModuleRes d T ⋙ completedTowerLimit T (exchangeConstantRing T A),
      ∀ (Z : d.towers T) (n : ℕ),
        e.hom.app Z ≫ limit.π ((exchangeTowerModuleRes d T).obj Z) (op n) =
          (reductionRestrict T (exchangeScalar d T)).map (limit.π Z (op n)) := by
  let := orderedAbSheafify T
  let := orderedAbLocallyBijective T
  have := orderedRestrictLimits T (exchangeScalar d T)
  exact uniqueLimitComparison (reductionRestrict T (exchangeScalar d T))

/-- The identity on compatible families, with its projection equations retained. -/
def ordinaryLambda (T : Scheme.{t}) :
    completedTowerLimit T (d.completedRing T) ⋙ reductionRestrict T (exchangeScalar d T) ≅
      exchangeTowerModuleRes d T ⋙ completedTowerLimit T (exchangeConstantRing T A) :=
  (ordinaryLambda_existsUnique d T).exists.choose

attribute [local irreducible] ordinaryLambda Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit

/-- The universal right-derived limit unit at a cochain complex. -/
def limitComplexUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (P : CochainComplex (exchangeTowers T R) ℤ) :
    DerivedCategory.Q.obj
        (((completedTowerLimit T R).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (completedRlim T R).obj (DerivedCategory.Q.obj P) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((completedTowerLimit T R).mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((completedTowerLimit T R).mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
    (completedTowerLimit T R).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj P) ≫
    (completedRlim T R).map ((DerivedCategory.quotientCompQhIso _).hom.app P)

attribute [local irreducible] limitComplexUnit

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The complex-level normalization of the specified lambda comparison. -/
def LambdaNormalization (T : Scheme.{t})
    (e : completedRlim T (d.completedRing T) ⋙ res d T ≅
        exchangeTowerRes d T ⋙ rlim (A := A) T) : Prop :=
  ∀ P : CochainComplex (d.towers T) ℤ,
        (res d T).map (limitComplexUnit T (d.completedRing T) P) ≫
            e.hom.app (DerivedCategory.Q.obj P) ≫
            (rlim (A := A) T).map
              ((exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app P) =
          (reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app
              (((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryLambda d T) (.up ℤ)).hom.app P) ≫
            limitComplexUnit T (exchangeConstantRing T A)
              (((exchangeTowerModuleRes d T).mapHomologicalComplex (.up ℤ)).obj P)

attribute [local irreducible] LambdaNormalization

attribute [local irreducible] SheafOfModules.fullyFaithfulForget
  SheafOfModules.instAddCommGroupHom

private def orderedDerivedComplexUnit
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ E) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso E).inv ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) F.rightDerivedFunctorUnit ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).hom F.rightDerivedFunctor

private theorem orderedDerivedComplexUnit_isIso
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ E) [F.Additive]
    (P : CochainComplex C ℤ) [P.IsKInjective] :
    IsIso ((orderedDerivedComplexUnit F).app P) := by
  dsimp only [orderedDerivedComplexUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

private theorem orderedScalarComparison
    {C E C' E' : Type*}
    [Category C] [Category E] [Category C'] [Category E']
    [Abelian C] [Abelian E] [Abelian C'] [Abelian E']
    [HasDerivedCategory C] [HasDerivedCategory E]
    [HasDerivedCategory C'] [HasDerivedCategory E']
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
    (F : C ⥤ E) (F' : C' ⥤ E') (r : C' ⥤ C) (s : E' ⥤ E)
    [F.Additive] [F'.Additive] [r.Additive] [s.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    [r.PreservesKInjectiveComplexes] (c : F' ⋙ s ≅ r ⋙ F) :
    ∃! e : F'.rightDerivedFunctor ⋙ s.mapDerivedCategory ≅
        r.mapDerivedCategory ⋙ F.rightDerivedFunctor,
      ∀ P : CochainComplex C' ℤ,
        s.mapDerivedCategory.map ((orderedDerivedComplexUnit F').app P) ≫
          e.hom.app (DerivedCategory.Q.obj P) ≫
          F.rightDerivedFunctor.map (r.mapDerivedCategoryFactors.hom.app P) =
        s.mapDerivedCategoryFactors.hom.app
            ((F'.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P) ≫
          (orderedDerivedComplexUnit F).app
            ((r.mapHomologicalComplex (.up ℤ)).obj P) := by
  let a : (F' ⋙ s).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (F'.rightDerivedFunctor ⋙ s.mapDerivedCategory) :=
    Functor.whiskerLeft (F'.mapHomologicalComplex (.up ℤ))
        s.mapDerivedCategoryFactors.inv ≫
      Functor.whiskerRight (orderedDerivedComplexUnit F') s.mapDerivedCategory
  let b : (F' ⋙ s).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (r.mapDerivedCategory ⋙ F.rightDerivedFunctor) :=
    Functor.whiskerRight (NatIso.mapHomologicalComplex c (.up ℤ)).hom DerivedCategory.Q ≫
      Functor.whiskerLeft (r.mapHomologicalComplex (.up ℤ)) (orderedDerivedComplexUnit F) ≫
      Functor.whiskerRight r.mapDerivedCategoryFactors.inv F.rightDerivedFunctor
  obtain ⟨e, he⟩ := CategoryTheory.FlatScalarTowerLimit.normalized_iso _ _ _ a b
    (by
      intro P hP
      have := hP
      have := orderedDerivedComplexUnit_isIso F' P
      dsimp only [a, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      infer_instance)
    (by
      intro P hP
      have := hP
      have := orderedDerivedComplexUnit_isIso F
        ((r.mapHomologicalComplex (.up ℤ)).obj P)
      dsimp only [b, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      infer_instance)
  have hn (P : CochainComplex C' ℤ) := he P
  dsimp only [a, b, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hn
  have hn' (P : CochainComplex C' ℤ) :
      s.mapDerivedCategory.map ((orderedDerivedComplexUnit F').app P) ≫
        e.hom.app (DerivedCategory.Q.obj P) ≫
        F.rightDerivedFunctor.map (r.mapDerivedCategoryFactors.hom.app P) =
      s.mapDerivedCategoryFactors.hom.app
          ((F'.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P) ≫
        (orderedDerivedComplexUnit F).app
          ((r.mapHomologicalComplex (.up ℤ)).obj P) := by
    apply (cancel_epi (s.mapDerivedCategoryFactors.inv.app _)).mp
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    have h := congrArg
      (fun k ↦ k ≫ F.rightDerivedFunctor.map (r.mapDerivedCategoryFactors.hom.app P)) (hn P)
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app] at h
    erw [F.rightDerivedFunctor.map_id, Category.comp_id] at h
    simp only [Category.assoc]
    exact h
  refine ⟨e, hn', ?_⟩
  intro e' he'
  apply Iso.ext
  apply CategoryTheory.FlatScalarTowerLimit.derived_ext
  intro P hP
  have := hP
  have := orderedDerivedComplexUnit_isIso F' P
  apply (cancel_epi (s.mapDerivedCategory.map ((orderedDerivedComplexUnit F').app P))).mp
  apply (cancel_mono (F.rightDerivedFunctor.map (r.mapDerivedCategoryFactors.hom.app P))).mp
  simpa only [Category.assoc] using (he' P).trans (hn' P).symm

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Restriction commutes with derived strict limit on arbitrary towers, with the
K-injective comparison fixed by its ordinary compatible-family map and universal units. -/
theorem lambda_existsUnique (T : Scheme.{t}) :
    ∃! e : completedRlim T (d.completedRing T) ⋙ res d T ≅
        exchangeTowerRes d T ⋙ rlim (A := A) T,
      LambdaNormalization d T e := by
  have := exchangeTowerModuleRes_kinjective d T
  have h := orderedScalarComparison
    (completedTowerLimit T (exchangeConstantRing T A))
    (completedTowerLimit T (d.completedRing T))
    (exchangeTowerModuleRes d T) (reductionRestrict T (exchangeScalar d T))
    (ordinaryLambda d T)
  unfold LambdaNormalization
  simpa only [orderedDerivedComplexUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, limitComplexUnit] using h

/-- The canonical restriction/derived-limit comparison on actual strict towers. -/
def lambda (T : Scheme.{t}) :
    completedRlim T (d.completedRing T) ⋙ res d T ≅ exchangeTowerRes d T ⋙ rlim (A := A) T :=
  (lambda_existsUnique d T).exists.choose

/-- Ordinary scalar restriction commutes with constant diagrams by identity components. -/
def ordinaryScalarDiagonal (T : Scheme.{t}) :
    d.constantTower T ⋙ exchangeTowerModuleRes d T ≅
      reductionRestrict T (exchangeScalar d T) ⋙ (Functor.const ℕᵒᵖ) :=
  NatIso.ofComponents
    (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp))
    (fun _ ↦ by ext n; simp)

/-- Exact descent of the identity scalar/diagonal comparison. -/
def scalarDiagonal (T : Scheme.{t}) :
    d.derivedConstantTower T ⋙ exchangeTowerRes d T ≅ res d T ⋙ diagonal (A := A) T :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (ordinaryScalarDiagonal d T) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

set_option linter.flexible false in
private theorem ordinaryLambda_unit (T : Scheme.{t})
    (N : reductionModules T (d.completedRing T)) :
    (reductionRestrict T (exchangeScalar d T)).map
        ((constLimAdj : (Functor.const ℕᵒᵖ) ⊣
          completedTowerLimit T (d.completedRing T)).unit.app N) ≫
      (ordinaryLambda d T).hom.app ((Functor.const ℕᵒᵖ).obj N) =
    (constLimAdj : (Functor.const ℕᵒᵖ) ⊣
        completedTowerLimit T (exchangeConstantRing T A)).unit.app
        ((reductionRestrict T (exchangeScalar d T)).obj N) ≫
      (completedTowerLimit T (exchangeConstantRing T A)).map
        ((ordinaryScalarDiagonal d T).symm.hom.app N) := by
  apply limit.hom_ext
  intro n
  have hl : (ordinaryLambda d T).hom.app ((Functor.const ℕᵒᵖ).obj N) ≫
      limit.π ((exchangeTowerModuleRes d T).obj ((Functor.const ℕᵒᵖ).obj N)) n =
      (reductionRestrict T (exchangeScalar d T)).map (limit.π ((Functor.const ℕᵒᵖ).obj N) n) := by
    unfold ordinaryLambda
    exact (ordinaryLambda_existsUnique d T).exists.choose_spec ((Functor.const ℕᵒᵖ).obj N) n.unop
  simp only [Category.assoc]
  erw [hl]
  simp [constLimAdj, ordinaryScalarDiagonal]
  rw [← Functor.map_comp, limit.lift_π]
  exact (reductionRestrict T (exchangeScalar d T)).map_id N

private theorem factorsh_hom_quotient {B E : Type*} [Category B] [Category E]
    [Abelian B] [Abelian E] [HasDerivedCategory B] [HasDerivedCategory E]
    (F : B ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex B ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  have h1 : (DerivedCategory.quotientCompQhIso B).hom.app K = 𝟙 _ := rfl
  have h2 : (DerivedCategory.quotientCompQhIso E).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  have h3 : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  rw [h1, h2, h3]
  simp

private theorem factorsh_inv_quotient {B E : Type*} [Category B] [Category E]
    [Abelian B] [Abelian E] [HasDerivedCategory B] [HasDerivedCategory E]
    (F : B ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex B ℤ) :
    F.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj K) =
      F.mapDerivedCategoryFactors.inv.app K := by
  have h := factorsh_hom_quotient F K
  apply (cancel_epi (F.mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient _ _).obj K))).mp
  rw [Iso.hom_inv_id_app]
  erw [h, Iso.hom_inv_id_app]
  rfl

private theorem limitComplexUnit_eq (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (P : CochainComplex (exchangeTowers T R) ℤ) :
    limitComplexUnit T R P =
      (completedTowerLimit T R).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj P) := by
  unfold limitComplexUnit
  have h1 : (DerivedCategory.quotientCompQhIso (reductionModules T R)).inv.app
      (((completedTowerLimit T R).mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  have h2 : ((completedTowerLimit T R).mapHomotopyCategoryFactors (.up ℤ)).inv.app P =
      𝟙 _ := rfl
  have h3 : (DerivedCategory.quotientCompQhIso (exchangeTowers T R)).hom.app P = 𝟙 _ := rfl
  rw [h1, h2, h3]
  simp

private theorem towerRes_unit_isIso (T : Scheme.{t}) :
    ∀ (K : CochainComplex (d.towers T) ℤ) [K.IsKInjective],
      IsIso ((completedTowerLimit T (exchangeConstantRing T A)).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((exchangeTowerModuleRes d T).mapHomologicalComplex (.up ℤ)).obj K))) := by
  have := exchangeTowerModuleRes_kinjective d T
  intro K _
  infer_instance

/-- The comparison of derived limits induced by the ordinary limit comparison. -/
private def lambdaIso (T : Scheme.{t}) :
    exchangeTowerRes d T ⋙ rlim (A := A) T ≅
      completedRlim T (d.completedRing T) ⋙ res d T :=
  (Functor.mapDerivedCategoryCompRightDerivedFunctorIsoOfIsIso (exchangeTowerModuleRes d T)
      (completedTowerLimit T (exchangeConstantRing T A)) (towerRes_unit_isIso d T)).symm ≪≫
    Functor.rightDerivedFunctorNatIso (ordinaryLambda d T).symm ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso (completedTowerLimit T (d.completedRing T))
      (reductionRestrict T (exchangeScalar d T))

private theorem lambdaIso_normalization (T : Scheme.{t}) :
    LambdaNormalization d T (lambdaIso d T).symm := by
  unfold LambdaNormalization
  intro P
  have hR := Functor.map_rightDerivedFunctorUnit_app_comp_restrictIso_inv_app
    (P₁ := reductionRestrict T (exchangeScalar d T)) (P₂ := exchangeTowerModuleRes d T)
    (F := completedTowerLimit T (exchangeConstantRing T A))
    (F' := completedTowerLimit T (d.completedRing T))
    (ordinaryLambda d T) (towerRes_unit_isIso d T) ((HomotopyCategory.quotient _ _).obj P)
  rw [limitComplexUnit_eq, limitComplexUnit_eq]
  simp only [Iso.symm_hom]
  rw [NatTrans.mapHomotopyCategorySquare_app_quotient_obj] at hR
  erw [factorsh_hom_quotient, factorsh_inv_quotient] at hR
  have hR' := congrArg (fun z ↦ z ≫ (rlim (A := A) T).map
    ((exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app P)) hR
  simp only [Category.assoc] at hR'
  erw [hR']
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

private theorem lambda_eq_lambdaIso (T : Scheme.{t}) : lambda d T = (lambdaIso d T).symm :=
  (lambda_existsUnique d T).unique (lambda_existsUnique d T).exists.choose_spec
    (lambdaIso_normalization d T)

private theorem lambda_mate (T : Scheme.{t}) :
    mateEquiv (d.constantRlimAdjunction T) (diagonalAdjunction (A := A) T)
        (Functor.mapDerivedCategorySquareIso (ordinaryScalarDiagonal d T).symm).hom =
      (lambda d T).hom := by
  rw [lambda_eq_lambdaIso]
  exact Adjunction.mateEquiv_mapDerivedCategoryRightDerivedAdjunction_restrict
    (constLimAdj : (Functor.const ℕᵒᵖ) ⊣ completedTowerLimit T (exchangeConstantRing T A))
    (constLimAdj : (Functor.const ℕᵒᵖ) ⊣ completedTowerLimit T (d.completedRing T))
    (ordinaryScalarDiagonal d T).symm (ordinaryLambda d T) (ordinaryLambda_unit d T)
    (towerRes_unit_isIso d T)

/-- Restriction carries the completed constant-tower adjunction unit to the constant one. -/
private theorem lambda_unit (T : Scheme.{t}) (K : d.derived T) :
    (res d T).map ((d.constantRlimAdjunction T).unit.app K) ≫
        (lambda d T).hom.app ((d.derivedConstantTower T).obj K) ≫
        (rlim (A := A) T).map ((scalarDiagonal d T).hom.app K) =
      (diagonalAdjunction (A := A) T).unit.app ((res d T).obj K) := by
  rw [← lambda_mate]
  have h := unit_mateEquiv (d.constantRlimAdjunction T) (diagonalAdjunction (A := A) T)
    (Functor.mapDerivedCategorySquareIso (ordinaryScalarDiagonal d T).symm).hom K
  rw [← Category.assoc]
  erw [h]
  rw [Category.assoc, ← Functor.map_comp]
  have hs : (Functor.mapDerivedCategorySquareIso (ordinaryScalarDiagonal d T).symm).hom.app K ≫
      (scalarDiagonal d T).hom.app K = 𝟙 _ := by
    have hsy := Functor.mapDerivedCategoryNatIso_symm (ordinaryScalarDiagonal d T)
    simp only [Functor.mapDerivedCategorySquareIso, scalarDiagonal, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc]
    rw [hsy]
    simp
  erw [hs, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

end AlgebraicGeometry.Scheme.OrderedExchange
